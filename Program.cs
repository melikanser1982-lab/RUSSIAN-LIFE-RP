using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Threading;
using OpenTK.Graphics.OpenGL4;
using OpenTK.Windowing.Common;
using OpenTK.Windowing.Desktop;
using OpenTK.Windowing.GraphicsLibraryFramework;
using OpenTK.Mathematics;
using StbImageSharp;
using SixLabors.ImageSharp;
using SixLabors.ImageSharp.PixelFormats;
using SixLabors.ImageSharp.Processing;
using ImGuiNET;

namespace MyMinecraft
{
    public enum GameState { Menu, CreateWorld, LoadWorld, Playing, Paused, Inventory, Settings, Multiplayer }

    public class RemotePlayer
    {
        public string Name = "";
        public Vector3 Position;
        public Vector3 TargetPosition;
        public long LastServerTime;
        public long LastLocalRecvMs;
        public int HeldBlock;
    }

    public class Game : GameWindow
    {
        private const int CHUNK_SIZE = 16;

        private int _shaderProgram, _lineShader, _colorShader, _texture;
        private int _lineVao, _lineVbo, _cubeVao, _cubeVbo;
        private int _texViewLoc, _texProjLoc, _texSamplerLoc, _lineViewLoc, _lineProjLoc;
        private int _colorModelLoc, _colorViewLoc, _colorProjLoc, _colorColorLoc;

        private ImGuiController _imGuiController = null!;
        private WorldManager _worldManager = new WorldManager();
        private NetworkClient _client = new NetworkClient();
        private Process? _serverProcess;

        private bool _isMultiplayer = false, _isHosting = false;
        private bool _showTabMenu = false, _showDebug = false;
        private bool _firstMove = true, _hostDumpPending = false;
        private string _connectIp = "127.0.0.1";
        private string _playerName = "Player" + new Random().Next(100, 999);
        private double _lastPosSend = 0, _breakStartTime = 0, _lastPlaceTime = 0;
        private int _lastSentHeldBlock = 0, _framesRendered = 0, _pendingBlockCount = 0;
        private int _hostDumpSizeX, _hostDumpSizeY, _hostDumpSizeZ;
        private int _selectedBlock = Blocks.Grass;
        private float _currentFps = 0f, _yaw = -90f, _pitch = 0f;
        private readonly Stopwatch _fpsStopwatch = new Stopwatch();
        private readonly Dictionary<string, RemotePlayer> _remote = new();
        private readonly ConcurrentQueue<Action> _mainThreadActions = new();

        // === ЧАНКИ ===
        private readonly Dictionary<(int cx, int cz), Chunk> _chunks = new();
        private Vector3 _lastChunkLoadPos = new Vector3(-9999, 0, -9999);
        private const int LOAD_RADIUS_CHUNKS = 8;   // радиус загрузки (в чанках)
        private const float UNLOAD_DISTANCE = 1.5f; // выгружать при удалении дальше чем radius * 1.5

        private int[,,]? _hostDumpBlocks;
        private int _bgTexture;
        private int[] _blockTextures = new int[7];
        private InventoryUI _inventoryUI = new InventoryUI();

        private GameState _state = GameState.Menu, _previousState = GameState.Menu;
        private string _newWorldName = "New World", _newWorldSeed = "";
        private bool _newWorldOldGen = false;
        private int _newWorldSize = 512;

        private Vector3 _position, _front = -Vector3.UnitZ, _up = Vector3.UnitY, _velocity = Vector3.Zero;
        private Vector2 _lastMousePos;

        private const float PlayerHeight = 1.8f, PlayerEyeHeight = 1.6f, PlayerRadius = 0.3f;
        private const float Gravity = 25f, JumpSpeed = 8f, MoveSpeed = 5.5f, InterpSpeed = 15f;
        private const long StaleTimeoutMs = 15000;

        private Vector3i _hitBlock = new Vector3i(-1, -1, -1), _placeBlock = new Vector3i(-1, -1, -1);

        private string _texturesPath = @"C:\Users\СЕЙРАН\Desktop\sharp\textures";
        private List<string> _savedWorlds = new List<string>();

        public Game(GameWindowSettings gws, NativeWindowSettings nws) : base(gws, nws) { }

        protected override void OnLoad()
        {
            base.OnLoad();
            _fpsStopwatch.Start();

            GL.ClearColor(0.4f, 0.6f, 0.9f, 1.0f);
            GL.Enable(EnableCap.DepthTest);
            GL.Disable(EnableCap.CullFace);

            SettingsManager.Load();

            SetupShaders();
            SetupColorShader();
            SetupLineRenderer();
            SetupCubeRenderer();
            CreateAtlasAndLoad();

            MakeCurrent();
            _imGuiController = new ImGuiController(ClientSize.X, ClientSize.Y);

            _bgTexture = _imGuiController.LoadTexture(Path.Combine(_texturesPath, "dirt.png"));
            LoadBlockTextures();

            CursorState = CursorState.Normal;

            _client.OnSeedReceived += (seed, time) =>
            {
                _mainThreadActions.Enqueue(() =>
                {
                    if (_worldManager.Blocks.GetLength(0) == 0)
                    {
                        _worldManager.CreateNewWorld("MultiplayerWorld", seed, false, 512);
                        _position = new Vector3(256, 40, 256);
                        _velocity = Vector3.Zero;
                        ClearAllChunks();
                        MarkAllChunksDirty();
                    }

                    _state = GameState.Playing;
                    CursorState = CursorState.Grabbed;
                    _firstMove = true;
                    _client.SendPlayer(_playerName, _position.X, _position.Y, _position.Z);

                    if (_hostDumpPending && _hostDumpBlocks != null)
                    {
                        _client.SendReset();
                        for (int x = 0; x < _hostDumpSizeX; x++)
                            for (int y = 0; y < _hostDumpSizeY; y++)
                                for (int z = 0; z < _hostDumpSizeZ; z++)
                                {
                                    int b = _hostDumpBlocks[x, y, z];
                                    if (b != 0) _client.SendBlock(x, y, z, b);
                                }
                        _hostDumpPending = false;
                        _hostDumpBlocks = null;
                    }
                });
            };

            _client.OnBlockChanged += (x, y, z, block, time) =>
            {
                Interlocked.Increment(ref _pendingBlockCount);
                _mainThreadActions.Enqueue(() =>
                {
                    int sx = _worldManager.Blocks.GetLength(0), sy = _worldManager.Blocks.GetLength(1), sz = _worldManager.Blocks.GetLength(2);
                    if (x >= 0 && x < sx && y >= 0 && y < sy && z >= 0 && z < sz)
                    {
                        _worldManager.Blocks[x, y, z] = block;
                        MarkChunkDirtyAt(x, z);
                    }
                    Interlocked.Decrement(ref _pendingBlockCount);
                });
            };

            _client.OnPlayerUpdate += (name, x, y, z, serverTime) =>
            {
                _mainThreadActions.Enqueue(() =>
                {
                    if (name == _playerName) return;
                    long localNow = DateTimeOffset.UtcNow.ToUnixTimeMilliseconds();
                    if (!_remote.TryGetValue(name, out var rp))
                    {
                        rp = new RemotePlayer { Name = name, Position = new Vector3(x, y, z), TargetPosition = new Vector3(x, y, z), LastServerTime = serverTime, LastLocalRecvMs = localNow };
                        _remote[name] = rp;
                        return;
                    }
                    if (serverTime < rp.LastServerTime) return;
                    rp.TargetPosition = new Vector3(x, y, z);
                    rp.LastServerTime = serverTime;
                    rp.LastLocalRecvMs = localNow;
                });
            };

            _client.OnPlayerJoin += (name) => { };
            _client.OnPlayerLeave += (name) => { _mainThreadActions.Enqueue(() => { _remote.Remove(name); }); };
            _client.OnHeldBlockUpdate += (name, block) => { _mainThreadActions.Enqueue(() => { if (_remote.TryGetValue(name, out var rp)) rp.HeldBlock = block; }); };

            _client.OnResetReceived += () =>
            {
                _mainThreadActions.Enqueue(() =>
                {
                    int sx = _worldManager.Blocks.GetLength(0), sy = _worldManager.Blocks.GetLength(1), sz = _worldManager.Blocks.GetLength(2);
                    for (int x = 0; x < sx; x++) for (int y = 0; y < sy; y++) for (int z = 0; z < sz; z++) _worldManager.Blocks[x, y, z] = 0;
                    MarkAllChunksDirty();
                });
            };
        }

        protected override void OnTextInput(TextInputEventArgs e)
        {
            base.OnTextInput(e);
            _imGuiController?.AddInputCharacter((char)e.Unicode);
        }

        private void ApplyFpsLimit()
        {
            if (SettingsManager.NoFpsLimit) VSync = VSyncMode.Off;
            else VSync = (SettingsManager.MaxFps == 60) ? VSyncMode.On : VSyncMode.Off;
        }

        // ============================================================
        // ЧАНКИ: управление
        // ============================================================

        private void ClearAllChunks()
        {
            foreach (var c in _chunks.Values)
            {
                if (c.Vao != 0) GL.DeleteVertexArray(c.Vao);
                if (c.Vbo != 0) GL.DeleteBuffer(c.Vbo);
                if (c.Ebo != 0) GL.DeleteBuffer(c.Ebo);
            }
            _chunks.Clear();
        }

        private void MarkChunkDirtyAt(int x, int z)
        {
            int cx = x / CHUNK_SIZE;
            int cz = z / CHUNK_SIZE;
            var key = (cx, cz);
            if (!_chunks.TryGetValue(key, out var c))
            {
                c = new Chunk(cx, cz);
                _chunks[key] = c;
            }
            c.Dirty = true;

            // Соседние чанки тоже грязные (пограничные грани)
            int lx = x % CHUNK_SIZE;
            int lz = z % CHUNK_SIZE;
            if (lx == 0) MarkNeighbourDirty(cx - 1, cz);
            if (lx == CHUNK_SIZE - 1) MarkNeighbourDirty(cx + 1, cz);
            if (lz == 0) MarkNeighbourDirty(cx, cz - 1);
            if (lz == CHUNK_SIZE - 1) MarkNeighbourDirty(cx, cz + 1);
        }

        private void MarkNeighbourDirty(int cx, int cz)
        {
            var key = (cx, cz);
            if (_chunks.TryGetValue(key, out var c))
                c.Dirty = true;
        }

        private void MarkAllChunksDirty()
        {
            int sx = _worldManager.Blocks.GetLength(0);
            int sz = _worldManager.Blocks.GetLength(2);
            int numCx = (sx + CHUNK_SIZE - 1) / CHUNK_SIZE;
            int numCz = (sz + CHUNK_SIZE - 1) / CHUNK_SIZE;
            for (int cx = 0; cx < numCx; cx++)
                for (int cz = 0; cz < numCz; cz++)
                {
                    var key = (cx, cz);
                    if (!_chunks.TryGetValue(key, out var c))
                    {
                        c = new Chunk(cx, cz);
                        _chunks[key] = c;
                    }
                    c.Dirty = true;
                }
        }

        private void UpdateChunksAroundPlayer()
        {
            if (_state != GameState.Playing) return;

            // Строим/выгружаем только когда игрок сдвинулся на чанк
            int playerCx = (int)(_position.X / CHUNK_SIZE);
            int playerCz = (int)(_position.Z / CHUNK_SIZE);

            if ((int)(_lastChunkLoadPos.X / CHUNK_SIZE) == playerCx &&
                (int)(_lastChunkLoadPos.Z / CHUNK_SIZE) == playerCz)
                return;

            _lastChunkLoadPos = _position;

            int sx = _worldManager.Blocks.GetLength(0);
            int sz = _worldManager.Blocks.GetLength(2);
            int numCx = (sx + CHUNK_SIZE - 1) / CHUNK_SIZE;
            int numCz = (sz + CHUNK_SIZE - 1) / CHUNK_SIZE;

            int loadR = LOAD_RADIUS_CHUNKS;
            int unloadR = (int)(LOAD_RADIUS_CHUNKS * UNLOAD_DISTANCE);

            // Загружаем ближайшие
            for (int cx = Math.Max(0, playerCx - loadR); cx <= Math.Min(numCx - 1, playerCx + loadR); cx++)
                for (int cz = Math.Max(0, playerCz - loadR); cz <= Math.Min(numCz - 1, playerCz + loadR); cz++)
                {
                    var key = (cx, cz);
                    if (!_chunks.TryGetValue(key, out var c))
                    {
                        c = new Chunk(cx, cz);
                        _chunks[key] = c;
                    }
                    c.Dirty = true;
                }

            // Выгружаем далёкие
            var toRemove = new List<(int, int)>();
            foreach (var kv in _chunks)
            {
                int dx = kv.Value.ChunkX - playerCx;
                int dz = kv.Value.ChunkZ - playerCz;
                if (dx * dx + dz * dz > unloadR * unloadR)
                    toRemove.Add(kv.Key);
            }
            foreach (var key in toRemove)
            {
                var c = _chunks[key];
                if (c.Vao != 0) GL.DeleteVertexArray(c.Vao);
                if (c.Vbo != 0) GL.DeleteBuffer(c.Vbo);
                if (c.Ebo != 0) GL.DeleteBuffer(c.Ebo);
                _chunks.Remove(key);
            }
        }

        // Строит один чанк
        private void BuildChunkMesh(Chunk chunk)
        {
            int sx = _worldManager.Blocks.GetLength(0);
            int sy = _worldManager.Blocks.GetLength(1);
            int sz = _worldManager.Blocks.GetLength(2);

            int startX = chunk.ChunkX * CHUNK_SIZE;
            int startZ = chunk.ChunkZ * CHUNK_SIZE;
            int endX = Math.Min(startX + CHUNK_SIZE, sx);
            int endZ = Math.Min(startZ + CHUNK_SIZE, sz);

            var verts = new List<float>();
            var idx = new List<uint>();
            uint offset = 0;

            for (int x = startX; x < endX; x++)
                for (int y = 0; y < sy; y++)
                    for (int z = startZ; z < endZ; z++)
                    {
                        int type = _worldManager.Blocks[x, y, z];
                        if (type == 0) continue;
                        AddBlockFacesTo(x, y, z, type, ref offset, sx, sy, sz, verts, idx);
                    }

            chunk.IndexCount = idx.Count;

            if (chunk.Vao == 0) chunk.Vao = GL.GenVertexArray();
            if (chunk.Vbo == 0) chunk.Vbo = GL.GenBuffer();
            if (chunk.Ebo == 0) chunk.Ebo = GL.GenBuffer();

            GL.BindVertexArray(chunk.Vao);

            GL.BindBuffer(BufferTarget.ArrayBuffer, chunk.Vbo);
            GL.BufferData(BufferTarget.ArrayBuffer, verts.Count * sizeof(float), verts.ToArray(), BufferUsageHint.StaticDraw);

            GL.BindBuffer(BufferTarget.ElementArrayBuffer, chunk.Ebo);
            GL.BufferData(BufferTarget.ElementArrayBuffer, idx.Count * sizeof(uint), idx.ToArray(), BufferUsageHint.StaticDraw);

            GL.VertexAttribPointer(0, 3, VertexAttribPointerType.Float, false, 5 * sizeof(float), 0);
            GL.EnableVertexAttribArray(0);
            GL.VertexAttribPointer(1, 2, VertexAttribPointerType.Float, false, 5 * sizeof(float), 3 * sizeof(float));
            GL.EnableVertexAttribArray(1);

            GL.BindVertexArray(0);

            chunk.HasMesh = true;
            chunk.Dirty = false;
        }

        private void AddBlockFacesTo(int x, int y, int z, int type, ref uint offset, int sizeX, int sizeY, int sizeZ, List<float> verts, List<uint> idx)
        {
            float u1, u2, v1, v2;
            bool up    = y < sizeY - 1 && _worldManager.Blocks[x, y + 1, z] == 0;
            bool down  = y > 0 && _worldManager.Blocks[x, y - 1, z] == 0;
            bool right = x < sizeX - 1 && _worldManager.Blocks[x + 1, y, z] == 0;
            bool left  = x > 0 && _worldManager.Blocks[x - 1, y, z] == 0;
            bool front = z < sizeZ - 1 && _worldManager.Blocks[x, y, z + 1] == 0;
            bool back  = z > 0 && _worldManager.Blocks[x, y, z - 1] == 0;

            if (up)    { Blocks.GetUVs(type, 0, out u1, out u2, out v1, out v2); float[] v = { x, y+1, z, u1, v1, x+1, y+1, z, u2, v1, x+1, y+1, z+1, u2, v2, x, y+1, z+1, u1, v2 }; verts.AddRange(v); AddIdx(idx, ref offset); }
            if (down)  { Blocks.GetUVs(type, 1, out u1, out u2, out v1, out v2); float[] v = { x, y, z, u1, v2, x+1, y, z, u2, v2, x+1, y, z+1, u2, v1, x, y, z+1, u1, v1 }; verts.AddRange(v); AddIdx(idx, ref offset); }
            if (right) { Blocks.GetUVs(type, 2, out u1, out u2, out v1, out v2); float[] v = { x+1, y, z, u1, v2, x+1, y+1, z, u1, v1, x+1, y+1, z+1, u2, v1, x+1, y, z+1, u2, v2 }; verts.AddRange(v); AddIdx(idx, ref offset); }
            if (left)  { Blocks.GetUVs(type, 3, out u1, out u2, out v1, out v2); float[] v = { x, y, z, u2, v2, x, y+1, z, u2, v1, x, y+1, z+1, u1, v1, x, y, z+1, u1, v2 }; verts.AddRange(v); AddIdx(idx, ref offset); }
            if (front) { Blocks.GetUVs(type, 4, out u1, out u2, out v1, out v2); float[] v = { x, y, z+1, u1, v2, x, y+1, z+1, u1, v1, x+1, y+1, z+1, u2, v1, x+1, y, z+1, u2, v2 }; verts.AddRange(v); AddIdx(idx, ref offset); }
            if (back)  { Blocks.GetUVs(type, 5, out u1, out u2, out v1, out v2); float[] v = { x+1, y, z, u2, v2, x+1, y+1, z, u2, v1, x, y+1, z, u1, v1, x, y, z, u1, v2 }; verts.AddRange(v); AddIdx(idx, ref offset); }
        }

        private void AddIdx(List<uint> idx, ref uint offset)
        {
            idx.Add(offset); idx.Add(offset + 1); idx.Add(offset + 2);
            idx.Add(offset); idx.Add(offset + 2); idx.Add(offset + 3);
            offset += 4;
        }

        // ============================================================
        // STUFF (как было)
        // ============================================================

        private void SetupShaders()
        {
            string vs = @"#version 330 core
                layout (location = 0) in vec3 aPos;
                layout (location = 1) in vec2 aTex;
                out vec2 TexCoord;
                uniform mat4 view;
                uniform mat4 projection;
                void main() { gl_Position = projection * view * vec4(aPos, 1.0); TexCoord = aTex; }";
            string fs = @"#version 330 core
                in vec2 TexCoord;
                out vec4 FragColor;
                uniform sampler2D texture1;
                void main() { FragColor = texture(texture1, TexCoord); }";
            int v = GL.CreateShader(ShaderType.VertexShader); GL.ShaderSource(v, vs); GL.CompileShader(v);
            int f = GL.CreateShader(ShaderType.FragmentShader); GL.ShaderSource(f, fs); GL.CompileShader(f);
            _shaderProgram = GL.CreateProgram();
            GL.AttachShader(_shaderProgram, v); GL.AttachShader(_shaderProgram, f); GL.LinkProgram(_shaderProgram);
            _texViewLoc = GL.GetUniformLocation(_shaderProgram, "view");
            _texProjLoc = GL.GetUniformLocation(_shaderProgram, "projection");
            _texSamplerLoc = GL.GetUniformLocation(_shaderProgram, "texture1");

            string lineVs = @"#version 330 core
                layout (location = 0) in vec3 aPos;
                uniform mat4 view;
                uniform mat4 projection;
                void main() { gl_Position = projection * view * vec4(aPos, 1.0); }";
            string lineFs = @"#version 330 core
                out vec4 FragColor;
                void main() { FragColor = vec4(0.0, 0.0, 0.0, 1.0); }";
            int lv = GL.CreateShader(ShaderType.VertexShader); GL.ShaderSource(lv, lineVs); GL.CompileShader(lv);
            int lf = GL.CreateShader(ShaderType.FragmentShader); GL.ShaderSource(lf, lineFs); GL.CompileShader(lf);
            _lineShader = GL.CreateProgram();
            GL.AttachShader(_lineShader, lv); GL.AttachShader(_lineShader, lf); GL.LinkProgram(_lineShader);
            _lineViewLoc = GL.GetUniformLocation(_lineShader, "view");
            _lineProjLoc = GL.GetUniformLocation(_lineShader, "projection");
        }

        private void SetupColorShader()
        {
            string vs = @"#version 330 core
                layout (location = 0) in vec3 aPos;
                uniform mat4 model;
                uniform mat4 view;
                uniform mat4 projection;
                void main() { gl_Position = projection * view * model * vec4(aPos, 1.0); }";
            string fs = @"#version 330 core
                out vec4 FragColor;
                uniform vec4 color;
                void main() { FragColor = color; }";
            int v = GL.CreateShader(ShaderType.VertexShader); GL.ShaderSource(v, vs); GL.CompileShader(v);
            int f = GL.CreateShader(ShaderType.FragmentShader); GL.ShaderSource(f, fs); GL.CompileShader(f);
            _colorShader = GL.CreateProgram();
            GL.AttachShader(_colorShader, v); GL.AttachShader(_colorShader, f); GL.LinkProgram(_colorShader);
            _colorModelLoc = GL.GetUniformLocation(_colorShader, "model");
            _colorViewLoc = GL.GetUniformLocation(_colorShader, "view");
            _colorProjLoc = GL.GetUniformLocation(_colorShader, "projection");
            _colorColorLoc = GL.GetUniformLocation(_colorShader, "color");
        }

        private void SetupLineRenderer()
        {
            _lineVao = GL.GenVertexArray();
            GL.BindVertexArray(_lineVao);
            _lineVbo = GL.GenBuffer();
            GL.BindBuffer(BufferTarget.ArrayBuffer, _lineVbo);
            GL.VertexAttribPointer(0, 3, VertexAttribPointerType.Float, false, 3 * sizeof(float), 0);
            GL.EnableVertexAttribArray(0);
            GL.BindVertexArray(0);
        }

        private void SetupCubeRenderer()
        {
            float[] vertices = {
                -0.5f, -0.5f, -0.5f,  0.5f, -0.5f, -0.5f,  0.5f,  0.5f, -0.5f,
                 0.5f,  0.5f, -0.5f, -0.5f,  0.5f, -0.5f, -0.5f, -0.5f, -0.5f,
                -0.5f, -0.5f,  0.5f,  0.5f, -0.5f,  0.5f,  0.5f,  0.5f,  0.5f,
                 0.5f,  0.5f,  0.5f, -0.5f,  0.5f,  0.5f, -0.5f, -0.5f,  0.5f,
                -0.5f,  0.5f,  0.5f, -0.5f,  0.5f, -0.5f, -0.5f, -0.5f, -0.5f,
                -0.5f, -0.5f, -0.5f, -0.5f, -0.5f,  0.5f, -0.5f,  0.5f,  0.5f,
                 0.5f,  0.5f,  0.5f,  0.5f,  0.5f, -0.5f,  0.5f, -0.5f, -0.5f,
                 0.5f, -0.5f, -0.5f,  0.5f, -0.5f,  0.5f,  0.5f,  0.5f,  0.5f,
                -0.5f, -0.5f, -0.5f,  0.5f, -0.5f, -0.5f,  0.5f, -0.5f,  0.5f,
                 0.5f, -0.5f,  0.5f, -0.5f, -0.5f,  0.5f, -0.5f, -0.5f, -0.5f,
                -0.5f,  0.5f, -0.5f,  0.5f,  0.5f, -0.5f,  0.5f,  0.5f,  0.5f,
                 0.5f,  0.5f,  0.5f, -0.5f,  0.5f,  0.5f, -0.5f,  0.5f, -0.5f
            };
            _cubeVao = GL.GenVertexArray();
            _cubeVbo = GL.GenBuffer();
            GL.BindVertexArray(_cubeVao);
            GL.BindBuffer(BufferTarget.ArrayBuffer, _cubeVbo);
            GL.BufferData(BufferTarget.ArrayBuffer, vertices.Length * sizeof(float), vertices, BufferUsageHint.StaticDraw);
            GL.VertexAttribPointer(0, 3, VertexAttribPointerType.Float, false, 3 * sizeof(float), 0);
            GL.EnableVertexAttribArray(0);
            GL.BindVertexArray(0);
        }

        private void CreateAtlasAndLoad()
        {
            int texSize = 64;
            int atlasW = Blocks.AtlasTextures.Length * texSize;
            using var atlas = new SixLabors.ImageSharp.Image<Rgba32>(atlasW, texSize);
            for (int i = 0; i < Blocks.AtlasTextures.Length; i++)
            {
                string path = Path.Combine(_texturesPath, Blocks.AtlasTextures[i]);
                if (File.Exists(path))
                {
                    using var img = SixLabors.ImageSharp.Image.Load<Rgba32>(path);
                    if (img.Width != texSize || img.Height != texSize)
                        img.Mutate(x => x.Resize(texSize, texSize));
                    atlas.Mutate(x => x.DrawImage(img, new Point(i * texSize, 0), 1f));
                }
            }
            string atlasPath = "atlas_temp.png";
            atlas.Save(atlasPath);
            using var stream = File.OpenRead(atlasPath);
            var image = StbImageSharp.ImageResult.FromStream(stream, StbImageSharp.ColorComponents.RedGreenBlueAlpha);
            _texture = GL.GenTexture();
            GL.BindTexture(TextureTarget.Texture2D, _texture);
            GL.TexImage2D(TextureTarget.Texture2D, 0, PixelInternalFormat.Rgba, image.Width, image.Height, 0, PixelFormat.Rgba, PixelType.UnsignedByte, image.Data);
            GL.TexParameter(TextureTarget.Texture2D, TextureParameterName.TextureMinFilter, (int)TextureMinFilter.Nearest);
            GL.TexParameter(TextureTarget.Texture2D, TextureParameterName.TextureMagFilter, (int)TextureMagFilter.Nearest);
        }

        private void LoadBlockTextures()
        {
            for (int i = 0; i < Blocks.UiTextures.Length; i++)
            {
                string path = Path.Combine(_texturesPath, Blocks.UiTextures[i]);
                if (File.Exists(path))
                    _blockTextures[i] = _imGuiController.LoadTexture(path);
            }
        }

        private void Raycast()
        {
            _hitBlock = new Vector3i(-1, -1, -1);
            _placeBlock = new Vector3i(-1, -1, -1);
            Vector3 eyePos = _position + new Vector3(0, PlayerEyeHeight - PlayerHeight, 0);
            int sizeX = _worldManager.Blocks.GetLength(0), sizeY = _worldManager.Blocks.GetLength(1), sizeZ = _worldManager.Blocks.GetLength(2);
            float step = 0.02f;
            for (float t = 0.0f; t < 6.0f; t += step)
            {
                Vector3 p = eyePos + _front * t;
                int x = (int)Math.Floor(p.X), y = (int)Math.Floor(p.Y), z = (int)Math.Floor(p.Z);
                if (x >= 0 && x < sizeX && y >= 0 && y < sizeY && z >= 0 && z < sizeZ && _worldManager.Blocks[x, y, z] != 0)
                {
                    _hitBlock = new Vector3i(x, y, z);
                    Vector3 prevP = eyePos + _front * (t - step);
                    int prevX = (int)Math.Floor(prevP.X), prevY = (int)Math.Floor(prevP.Y), prevZ = (int)Math.Floor(prevP.Z);
                    if (prevX < x) _placeBlock = new Vector3i(x - 1, y, z);
                    else if (prevX > x) _placeBlock = new Vector3i(x + 1, y, z);
                    else if (prevY < y) _placeBlock = new Vector3i(x, y - 1, z);
                    else if (prevY > y) _placeBlock = new Vector3i(x, y + 1, z);
                    else if (prevZ < z) _placeBlock = new Vector3i(x, y, z - 1);
                    else if (prevZ > z) _placeBlock = new Vector3i(x, y, z + 1);
                    break;
                }
            }
        }

        private void PushMenuStyle()
        {
            ImGui.PushStyleColor(ImGuiCol.WindowBg, new System.Numerics.Vector4(0.2f, 0.2f, 0.2f, 1.0f));
            ImGui.PushStyleColor(ImGuiCol.TitleBg, new System.Numerics.Vector4(0.15f, 0.15f, 0.15f, 1.0f));
            ImGui.PushStyleColor(ImGuiCol.TitleBgActive, new System.Numerics.Vector4(0.15f, 0.15f, 0.15f, 1.0f));
            ImGui.PushStyleColor(ImGuiCol.Button, new System.Numerics.Vector4(0.45f, 0.45f, 0.45f, 1.0f));
            ImGui.PushStyleColor(ImGuiCol.ButtonHovered, new System.Numerics.Vector4(0.55f, 0.55f, 0.55f, 1.0f));
            ImGui.PushStyleColor(ImGuiCol.ButtonActive, new System.Numerics.Vector4(0.35f, 0.35f, 0.35f, 1.0f));
            ImGui.PushStyleColor(ImGuiCol.Text, new System.Numerics.Vector4(1, 1, 1, 1));
            ImGui.PushStyleVar(ImGuiStyleVar.FrameBorderSize, 2.0f);
            ImGui.PushStyleVar(ImGuiStyleVar.FrameRounding, 0.0f);
            ImGui.PushStyleVar(ImGuiStyleVar.WindowPadding, new System.Numerics.Vector2(20, 20));
            ImGui.PushStyleVar(ImGuiStyleVar.ItemSpacing, new System.Numerics.Vector2(0, 15));
            ImGui.PushStyleVar(ImGuiStyleVar.WindowRounding, 0.0f);
        }

        private void PopMenuStyle()
        {
            ImGui.PopStyleVar(5);
            ImGui.PopStyleColor(7);
        }

        private void DrawPlayerCube(Vector3 pos, Matrix4 view, Matrix4 projection, int heldBlock)
        {
            pos.Y -= PlayerHeight;
            DrawColoredCube(Matrix4.CreateScale(0.5f, 0.75f, 0.3f) * Matrix4.CreateTranslation(pos.X, pos.Y + 1.125f, pos.Z), view, projection, new Vector4(0.2f, 0.4f, 0.8f, 1.0f));
            DrawColoredCube(Matrix4.CreateScale(0.5f, 0.5f, 0.5f) * Matrix4.CreateTranslation(pos.X, pos.Y + 1.75f, pos.Z), view, projection, new Vector4(0.9f, 0.7f, 0.5f, 1.0f));
            DrawColoredCube(Matrix4.CreateScale(0.25f, 0.75f, 0.25f) * Matrix4.CreateTranslation(pos.X - 0.15f, pos.Y + 0.375f, pos.Z), view, projection, new Vector4(0.2f, 0.2f, 0.4f, 1.0f));
            DrawColoredCube(Matrix4.CreateScale(0.25f, 0.75f, 0.25f) * Matrix4.CreateTranslation(pos.X + 0.15f, pos.Y + 0.375f, pos.Z), view, projection, new Vector4(0.2f, 0.2f, 0.4f, 1.0f));
            if (heldBlock > 0) DrawColoredCube(Matrix4.CreateScale(0.25f) * Matrix4.CreateTranslation(pos.X + 0.35f, pos.Y + 0.9f, pos.Z + 0.3f), view, projection, Blocks.GetColor(heldBlock));
        }

        private void DrawColoredCube(Matrix4 model, Matrix4 view, Matrix4 projection, Vector4 color)
        {
            GL.UseProgram(_colorShader);
            GL.UniformMatrix4(_colorModelLoc, false, ref model);
            GL.UniformMatrix4(_colorViewLoc, false, ref view);
            GL.UniformMatrix4(_colorProjLoc, false, ref projection);
            GL.Uniform4(_colorColorLoc, color);
            GL.BindVertexArray(_cubeVao);
            GL.DrawArrays(PrimitiveType.Triangles, 0, 36);
        }

        private void DrawBlockOutline(Vector3i block, Matrix4 view, Matrix4 proj)
        {
            float s = 1.002f; float ox = block.X, oy = block.Y, oz = block.Z;
            float[] vertices = { ox, oy, oz, ox+s, oy, oz, ox+s, oy, oz, ox+s, oy, oz+s, ox+s, oy, oz+s, ox, oy, oz+s, ox, oy, oz+s, ox, oy, oz, ox, oy+s, oz, ox+s, oy+s, oz, ox+s, oy+s, oz, ox+s, oy+s, oz+s, ox+s, oy+s, oz+s, ox, oy+s, oz+s, ox, oy+s, oz+s, ox, oy+s, oz, ox, oy, oz, ox, oy+s, oz, ox+s, oy, oz, ox+s, oy+s, oz, ox+s, oy, oz+s, ox+s, oy+s, oz+s, ox, oy, oz+s, ox, oy+s, oz+s };
            GL.UseProgram(_lineShader);
            GL.UniformMatrix4(_lineViewLoc, false, ref view);
            GL.UniformMatrix4(_lineProjLoc, false, ref proj);
            GL.BindVertexArray(_lineVao);
            GL.BindBuffer(BufferTarget.ArrayBuffer, _lineVbo);
            GL.BufferData(BufferTarget.ArrayBuffer, vertices.Length * sizeof(float), vertices, BufferUsageHint.DynamicDraw);
            GL.DrawArrays(PrimitiveType.Lines, 0, vertices.Length / 3);
        }

        private void DumpLocalWorld()
        {
            int sx = _worldManager.Blocks.GetLength(0), sy = _worldManager.Blocks.GetLength(1), sz = _worldManager.Blocks.GetLength(2);
            if (sx == 0) return;
            _hostDumpBlocks = (int[,,])_worldManager.Blocks.Clone();
            _hostDumpSizeX = sx; _hostDumpSizeY = sy; _hostDumpSizeZ = sz; _hostDumpPending = true;
        }

        private void MoveWithCollision(Vector3 delta)
        {
            if (delta.X != 0) { Vector3 newPos = _position + new Vector3(delta.X, 0, 0); if (!Collides(newPos)) _position = newPos; }
            if (delta.Z != 0) { Vector3 newPos = _position + new Vector3(0, 0, delta.Z); if (!Collides(newPos)) _position = newPos; }
            if (delta.Y != 0) { Vector3 newPos = _position + new Vector3(0, delta.Y, 0); if (!Collides(newPos)) _position = newPos; else { if (delta.Y < 0) _velocity.Y = 0; else if (delta.Y > 0) _velocity.Y = 0; } }
        }

        private bool Collides(Vector3 pos)
        {
            float minX = pos.X - PlayerRadius, maxX = pos.X + PlayerRadius, minY = pos.Y - PlayerHeight, maxY = pos.Y, minZ = pos.Z - PlayerRadius, maxZ = pos.Z + PlayerRadius;
            int sizeX = _worldManager.Blocks.GetLength(0), sizeY = _worldManager.Blocks.GetLength(1), sizeZ = _worldManager.Blocks.GetLength(2);
            if (minX < 1.5f || maxX > sizeX - 1.5f || minZ < 1.5f || maxZ > sizeZ - 1.5f) return true;
            int x0 = (int)MathF.Floor(minX), x1 = (int)MathF.Floor(maxX), y0 = (int)MathF.Floor(minY), y1 = (int)MathF.Floor(maxY), z0 = (int)MathF.Floor(minZ), z1 = (int)MathF.Floor(maxZ);
            for (int x = x0; x <= x1; x++) for (int y = y0; y <= y1; y++) for (int z = z0; z <= z1; z++) { if (x < 0 || x >= sizeX || y < 0 || y >= sizeY || z < 0 || z >= sizeZ) continue; if (_worldManager.Blocks[x, y, z] != 0) return true; }
            return false;
        }

        private bool IsOnGround() => Collides(_position + new Vector3(0, -0.05f, 0));

        private bool BlockIntersectsPlayer(Vector3i block)
        {
            if (block.X <= 0 || block.X >= _worldManager.CurrentData.SizeX - 1 || block.Z <= 0 || block.Z >= _worldManager.CurrentData.SizeZ - 1) return true;
            float minX = _position.X - PlayerRadius, maxX = _position.X + PlayerRadius, minY = _position.Y - PlayerHeight, maxY = _position.Y, minZ = _position.Z - PlayerRadius, maxZ = _position.Z + PlayerRadius;
            return !(block.X + 1 <= minX || block.X >= maxX || block.Y + 1 <= minY || block.Y >= maxY || block.Z + 1 <= minZ || block.Z >= maxZ);
        }

        protected override void OnRenderFrame(FrameEventArgs args)
        {
            base.OnRenderFrame(args);
            _framesRendered++;
            if (_fpsStopwatch.ElapsedMilliseconds >= 500)
            {
                _currentFps = _framesRendered / (_fpsStopwatch.ElapsedMilliseconds / 1000f);
                _framesRendered = 0;
                _fpsStopwatch.Restart();
            }

            _imGuiController.Update(this, (float)args.Time, _state == GameState.Playing);
            GL.Clear(ClearBufferMask.ColorBufferBit | ClearBufferMask.DepthBufferBit);

            if (_state == GameState.Playing || _state == GameState.Paused || _state == GameState.Inventory || _state == GameState.Settings)
            {
                Vector3 eye = new Vector3(_position.X, _position.Y - PlayerHeight + PlayerEyeHeight, _position.Z);
                var view = Matrix4.LookAt(eye, eye + _front, _up);
                var projection = Matrix4.CreatePerspectiveFieldOfView(MathHelper.DegreesToRadians(SettingsManager.Fov), (float)ClientSize.X / ClientSize.Y, 0.1f, SettingsManager.RenderDistance);

                // Солнце
                Vector3 sunPos = eye + new Vector3(200f, 300f, 200f);
                DrawColoredCube(Matrix4.CreateScale(20f) * Matrix4.CreateTranslation(sunPos), view, projection, new Vector4(1f, 0.95f, 0.3f, 1f));

                // Чанки
                GL.UseProgram(_shaderProgram);
                GL.UniformMatrix4(_texViewLoc, false, ref view);
                GL.UniformMatrix4(_texProjLoc, false, ref projection);
                GL.ActiveTexture(TextureUnit.Texture0);
                GL.BindTexture(TextureTarget.Texture2D, _texture);
                GL.Uniform1(_texSamplerLoc, 0);

                float renderDistSq = SettingsManager.RenderDistance * SettingsManager.RenderDistance;
                foreach (var chunk in _chunks.Values)
                {
                    if (!chunk.HasMesh || chunk.IndexCount == 0) continue;
                    float dx = chunk.WorldCenterX - _position.X;
                    float dz = chunk.WorldCenterZ - _position.Z;
                    if (dx * dx + dz * dz > renderDistSq) continue;

                    GL.BindVertexArray(chunk.Vao);
                    GL.DrawElements(PrimitiveType.Triangles, chunk.IndexCount, DrawElementsType.UnsignedInt, 0);
                }

                if (_hitBlock.X != -1 && _state == GameState.Playing) DrawBlockOutline(_hitBlock, view, projection);
                foreach (var rp in _remote.Values) { if (rp.Name != _playerName) DrawPlayerCube(rp.Position, view, projection, rp.HeldBlock); }
            }

            DrawUI();
            _imGuiController.Render();
            SwapBuffers();
        }

        private void DrawUI()
        {
            if (_state != GameState.Playing && _state != GameState.Inventory)
            {
                if (_bgTexture != 0)
                {
                    var drawList = ImGui.GetBackgroundDrawList();
                    float texSize = 64f;
                    for (float x = 0; x < ClientSize.X; x += texSize)
                        for (float y = 0; y < ClientSize.Y; y += texSize)
                            drawList.AddImage((IntPtr)_bgTexture, new System.Numerics.Vector2(x, y), new System.Numerics.Vector2(x + texSize, y + texSize));
                }
            }

            if (_state == GameState.Menu)
            {
                ImGui.SetNextWindowPos(new System.Numerics.Vector2(ClientSize.X / 2f, 80), ImGuiCond.Always, new System.Numerics.Vector2(0.5f, 0f));
                ImGui.SetNextWindowSize(new System.Numerics.Vector2(800, 150));
                ImGui.Begin("Logo", ImGuiWindowFlags.NoTitleBar | ImGuiWindowFlags.NoResize | ImGuiWindowFlags.NoMove | ImGuiWindowFlags.NoBackground | ImGuiWindowFlags.NoDecoration);
                ImGui.SetWindowFontScale(4.5f);
                ImGui.SetCursorPosX((800 - ImGui.CalcTextSize("CScraft").X) / 2f);
                ImGui.TextColored(new System.Numerics.Vector4(0.95f, 0.95f, 0.95f, 1.0f), "CScraft");
                ImGui.SetWindowFontScale(1.0f);
                ImGui.End();

                ImGui.SetNextWindowPos(new System.Numerics.Vector2(ClientSize.X / 2f, ClientSize.Y / 2f + 40), ImGuiCond.Always, new System.Numerics.Vector2(0.5f, 0.5f));
                ImGui.SetNextWindowSize(new System.Numerics.Vector2(600, 450));
                PushMenuStyle();
                ImGui.Begin("MainMenu", ImGuiWindowFlags.NoTitleBar | ImGuiWindowFlags.NoResize | ImGuiWindowFlags.NoMove | ImGuiWindowFlags.NoBackground | ImGuiWindowFlags.NoDecoration);
                float buttonW = 480, buttonH = 50;

                ImGui.SetCursorPosX(60); if (ImGui.Button(Lang.T("Singleplayer"), new System.Numerics.Vector2(buttonW, buttonH))) _state = GameState.CreateWorld;
                ImGui.SetCursorPosX(60); if (ImGui.Button(Lang.T("LoadWorld"), new System.Numerics.Vector2(buttonW, buttonH))) { _savedWorlds = _worldManager.GetSavedWorlds(); _state = GameState.LoadWorld; }
                ImGui.SetCursorPosX(60); if (ImGui.Button(Lang.T("Multiplayer"), new System.Numerics.Vector2(buttonW, buttonH))) _state = GameState.Multiplayer;
                ImGui.SetCursorPosX(60); if (ImGui.Button(Lang.T("Options"), new System.Numerics.Vector2(buttonW, buttonH))) { _previousState = GameState.Menu; _state = GameState.Settings; }
                ImGui.SetCursorPosX(60); if (ImGui.Button(Lang.T("Quit"), new System.Numerics.Vector2(buttonW, buttonH))) Close();

                PopMenuStyle();
                ImGui.End();
            }
            else if (_state == GameState.Settings)
            {
                ImGui.SetNextWindowPos(new System.Numerics.Vector2(ClientSize.X / 2f, ClientSize.Y / 2f), ImGuiCond.Always, new System.Numerics.Vector2(0.5f, 0.5f));
                ImGui.SetNextWindowSize(new System.Numerics.Vector2(600, 700));
                PushMenuStyle();
                ImGui.Begin("Options", ImGuiWindowFlags.NoResize | ImGuiWindowFlags.NoCollapse);
                ImGui.SetWindowFontScale(2.5f); ImGui.TextColored(new System.Numerics.Vector4(1, 1, 1, 1), Lang.T("Options")); ImGui.SetWindowFontScale(1.0f);
                ImGui.Dummy(new System.Numerics.Vector2(0, 10));
                ImGui.Checkbox(Lang.T("NoFpsLimit"), ref SettingsManager.NoFpsLimit);
                if (ImGui.IsItemDeactivatedAfterEdit()) { SettingsManager.Save(); ApplyFpsLimit(); }
                if (!SettingsManager.NoFpsLimit) { if (ImGui.SliderInt(Lang.T("MaxFps"), ref SettingsManager.MaxFps, 30, 240)) { SettingsManager.Save(); ApplyFpsLimit(); } }
                else ImGui.TextColored(new System.Numerics.Vector4(0.5f, 0.5f, 0.5f, 1), "FPS Limit Disabled");
                ImGui.SliderFloat(Lang.T("MouseSens"), ref SettingsManager.MouseSensitivity, 0.05f, 0.5f, "%.2f"); if (ImGui.IsItemDeactivatedAfterEdit()) SettingsManager.Save();
                ImGui.Checkbox(Lang.T("ShowFps"), ref SettingsManager.ShowFps); if (ImGui.IsItemDeactivatedAfterEdit()) SettingsManager.Save();
                ImGui.SliderFloat(Lang.T("Fov"), ref SettingsManager.Fov, 50f, 100f, "%.0f"); if (ImGui.IsItemDeactivatedAfterEdit()) SettingsManager.Save();
                ImGui.SliderFloat(Lang.T("RenderDist"), ref SettingsManager.RenderDistance, 50f, 500f, "%.0f"); if (ImGui.IsItemDeactivatedAfterEdit()) SettingsManager.Save();
                ImGui.Dummy(new System.Numerics.Vector2(0, 10));
                ImGui.Text(Lang.T("Language"));
                if (ImGui.RadioButton("Русский", SettingsManager.Language == "ru")) { SettingsManager.Language = "ru"; Lang.Current = "ru"; SettingsManager.Save(); }
                ImGui.SameLine();
                if (ImGui.RadioButton("English", SettingsManager.Language == "en")) { SettingsManager.Language = "en"; Lang.Current = "en"; SettingsManager.Save(); }
                ImGui.Dummy(new System.Numerics.Vector2(0, 30));
                if (ImGui.Button(Lang.T("Done"), new System.Numerics.Vector2(480, 50))) { _state = _previousState; if (_state == GameState.Playing) { CursorState = CursorState.Grabbed; _firstMove = true; } else CursorState = CursorState.Normal; }
                PopMenuStyle();
                ImGui.End();
            }
            else if (_state == GameState.Paused)
            {
                ImGui.SetNextWindowPos(new System.Numerics.Vector2(ClientSize.X / 2f, ClientSize.Y / 2f), ImGuiCond.Always, new System.Numerics.Vector2(0.5f, 0.5f));
                ImGui.SetNextWindowSize(new System.Numerics.Vector2(600, 480));
                PushMenuStyle();
                ImGui.Begin("Pause", ImGuiWindowFlags.NoResize | ImGuiWindowFlags.NoCollapse);
                ImGui.SetWindowFontScale(2.5f); ImGui.TextColored(new System.Numerics.Vector4(1, 1, 1, 1), Lang.T("GameMenu")); ImGui.SetWindowFontScale(1.0f);
                ImGui.Dummy(new System.Numerics.Vector2(0, 10));
                float buttonW = 480, buttonH = 50;
                if (ImGui.Button(Lang.T("BackToGame"), new System.Numerics.Vector2(buttonW, buttonH))) { _state = GameState.Playing; CursorState = CursorState.Grabbed; _firstMove = true; }
                if (ImGui.Button(Lang.T("Options"), new System.Numerics.Vector2(buttonW, buttonH))) { _previousState = GameState.Paused; _state = GameState.Settings; }
                if (ImGui.Button(Lang.T("Save"), new System.Numerics.Vector2(buttonW, buttonH))) _worldManager.SaveWorld(_position, _yaw, _pitch);
                if (ImGui.Button(Lang.T("Disconnect"), new System.Numerics.Vector2(buttonW, buttonH))) { _isHosting = false; _state = GameState.Menu; CursorState = CursorState.Normal; _client.Disconnect(); _remote.Clear(); _isMultiplayer = false; if (_serverProcess != null && !_serverProcess.HasExited) { try { _serverProcess.Kill(); _serverProcess.WaitForExit(3000); } catch { } _serverProcess = null; } }
                PopMenuStyle();
                ImGui.End();
            }
            else if (_state == GameState.CreateWorld)
            {
                ImGui.SetNextWindowPos(new System.Numerics.Vector2(ClientSize.X / 2f, ClientSize.Y / 2f), ImGuiCond.Always, new System.Numerics.Vector2(0.5f, 0.5f));
                ImGui.SetNextWindowSize(new System.Numerics.Vector2(600, 600));
                PushMenuStyle();
                ImGui.Begin("Create World", ImGuiWindowFlags.NoResize | ImGuiWindowFlags.NoCollapse);
                ImGui.SetWindowFontScale(2.5f); ImGui.TextColored(new System.Numerics.Vector4(1, 1, 1, 1), Lang.T("CreateWorld")); ImGui.SetWindowFontScale(1.0f);
                ImGui.Dummy(new System.Numerics.Vector2(0, 10));
                ImGui.InputText(Lang.T("WorldName"), ref _newWorldName, 32);
                if (string.IsNullOrEmpty(_newWorldSeed)) _newWorldSeed = new Random().Next(1000, 999999).ToString();
                ImGui.InputText(Lang.T("Seed"), ref _newWorldSeed, 20);
                ImGui.Dummy(new System.Numerics.Vector2(0, 10));
                ImGui.Text(Lang.T("GenNew") + " / " + Lang.T("GenOld"));
                if (ImGui.RadioButton(Lang.T("GenNew"), !_newWorldOldGen)) _newWorldOldGen = false;
                if (ImGui.RadioButton(Lang.T("GenOld"), _newWorldOldGen)) _newWorldOldGen = true;
                ImGui.Dummy(new System.Numerics.Vector2(0, 10));
                ImGui.Text(Lang.T("Size256") + " / " + Lang.T("Size512"));
                if (ImGui.RadioButton(Lang.T("Size256"), _newWorldSize == 256)) _newWorldSize = 256;
                if (ImGui.RadioButton(Lang.T("Size512"), _newWorldSize == 512)) _newWorldSize = 512;
                ImGui.Dummy(new System.Numerics.Vector2(0, 20));
                if (ImGui.Button(Lang.T("Create"), new System.Numerics.Vector2(480, 50))) { int seed = _newWorldSeed.GetHashCode(); _worldManager.CreateNewWorld(_newWorldName, seed, _newWorldOldGen, _newWorldSize); _position = new Vector3(_newWorldSize / 2f, 40, _newWorldSize / 2f); _velocity = Vector3.Zero; _state = GameState.Playing; CursorState = CursorState.Grabbed; _firstMove = true; ClearAllChunks(); MarkAllChunksDirty(); }
                if (ImGui.Button(Lang.T("Cancel"), new System.Numerics.Vector2(480, 50))) _state = GameState.Menu;
                PopMenuStyle();
                ImGui.End();
            }
            else if (_state == GameState.Multiplayer)
            {
                ImGui.SetNextWindowPos(new System.Numerics.Vector2(ClientSize.X / 2f, ClientSize.Y / 2f), ImGuiCond.Always, new System.Numerics.Vector2(0.5f, 0.5f));
                ImGui.SetNextWindowSize(new System.Numerics.Vector2(600, 420));
                PushMenuStyle();
                ImGui.Begin("Multiplayer", ImGuiWindowFlags.NoResize | ImGuiWindowFlags.NoCollapse);
                ImGui.SetWindowFontScale(2.5f); ImGui.TextColored(new System.Numerics.Vector4(1, 1, 1, 1), Lang.T("Multiplayer")); ImGui.SetWindowFontScale(1.0f);
                ImGui.Dummy(new System.Numerics.Vector2(0, 10));
                ImGui.InputText(Lang.T("IP"), ref _connectIp, 32);
                ImGui.InputText(Lang.T("Nick"), ref _playerName, 32);
                ImGui.Dummy(new System.Numerics.Vector2(0, 10));
                if (ImGui.Button(Lang.T("Connect"), new System.Numerics.Vector2(480, 50))) { if (_client.Connect(_connectIp)) { _isMultiplayer = true; _client.SendJoin(_playerName); } }
                if (ImGui.Button(Lang.T("Cancel"), new System.Numerics.Vector2(480, 50))) _state = GameState.Menu;
                PopMenuStyle();
                ImGui.End();
            }
            else if (_state == GameState.LoadWorld)
            {
                ImGui.SetNextWindowPos(new System.Numerics.Vector2(ClientSize.X / 2f, ClientSize.Y / 2f), ImGuiCond.Always, new System.Numerics.Vector2(0.5f, 0.5f));
                ImGui.SetNextWindowSize(new System.Numerics.Vector2(600, 500));
                PushMenuStyle();
                ImGui.Begin("Select World", ImGuiWindowFlags.NoResize | ImGuiWindowFlags.NoCollapse);
                ImGui.SetWindowFontScale(2.5f); ImGui.TextColored(new System.Numerics.Vector4(1, 1, 1, 1), Lang.T("LoadWorld")); ImGui.SetWindowFontScale(1.0f);
                ImGui.Dummy(new System.Numerics.Vector2(0, 10));
                if (_savedWorlds.Count == 0) ImGui.Text(Lang.T("NoWorlds"));
                else
                {
                    string? toDelete = null;
                    foreach (var world in _savedWorlds)
                    {
                        ImGui.PushID(world);
                        if (ImGui.Button(world, new System.Numerics.Vector2(380, 40)))
                        {
                            _worldManager.LoadWorld(Path.Combine(_worldManager.SavesPath, world + ".json"));
                            _position = new Vector3(_worldManager.CurrentData.PlayerX, _worldManager.CurrentData.PlayerY, _worldManager.CurrentData.PlayerZ);
                            _yaw = _worldManager.CurrentData.PlayerYaw;
                            _pitch = _worldManager.CurrentData.PlayerPitch;
                            _velocity = Vector3.Zero;
                            _state = GameState.Playing;
                            CursorState = CursorState.Grabbed;
                            _firstMove = true;
                            ClearAllChunks();
                            MarkAllChunksDirty();
                        }
                        ImGui.SameLine();
                        if (ImGui.Button(Lang.T("Delete"), new System.Numerics.Vector2(90, 40))) toDelete = world;
                        ImGui.PopID();
                    }
                    if (toDelete != null) { File.Delete(Path.Combine(_worldManager.SavesPath, toDelete + ".json")); _savedWorlds = _worldManager.GetSavedWorlds(); }
                }
                ImGui.Dummy(new System.Numerics.Vector2(0, 20));
                if (ImGui.Button(Lang.T("Cancel"), new System.Numerics.Vector2(480, 50))) _state = GameState.Menu;
                PopMenuStyle();
                ImGui.End();
            }
            else if (_state == GameState.Inventory)
            {
                string closeReason;
                bool closed = _inventoryUI.Draw(ref _selectedBlock, _blockTextures, out closeReason);
                if (closed || closeReason == "button" || closeReason == "X") { _state = GameState.Playing; CursorState = CursorState.Grabbed; _firstMove = true; }
            }
            else if (_state == GameState.Playing)
            {
                var drawList = ImGui.GetForegroundDrawList();
                var center = new System.Numerics.Vector2(ClientSize.X / 2f, ClientSize.Y / 2f);
                drawList.AddLine(center - new System.Numerics.Vector2(10, 0), center + new System.Numerics.Vector2(10, 0), 0xFFFFFFFF, 2f);
                drawList.AddLine(center - new System.Numerics.Vector2(0, 10), center + new System.Numerics.Vector2(0, 10), 0xFFFFFFFF, 2f);

                if (_pendingBlockCount > 0)
                {
                    ImGui.SetNextWindowPos(new System.Numerics.Vector2(ClientSize.X / 2f, 50), ImGuiCond.Always, new System.Numerics.Vector2(0.5f, 0f));
                    ImGui.SetNextWindowSize(new System.Numerics.Vector2(420, 0));
                    ImGui.Begin("Loading", ImGuiWindowFlags.NoResize | ImGuiWindowFlags.NoCollapse | ImGuiWindowFlags.NoTitleBar | ImGuiWindowFlags.NoMove | ImGuiWindowFlags.AlwaysAutoResize);
                    ImGui.Text($"Загрузка мира... осталось {_pendingBlockCount} блоков");
                    ImGui.End();
                }

                if (_showDebug || SettingsManager.ShowFps)
                {
                    ImGui.SetNextWindowPos(new System.Numerics.Vector2(10, 10), ImGuiCond.Always);
                    ImGui.SetNextWindowSize(new System.Numerics.Vector2(0, 0));
                    ImGui.Begin("Debug", ImGuiWindowFlags.NoResize | ImGuiWindowFlags.NoCollapse | ImGuiWindowFlags.NoTitleBar | ImGuiWindowFlags.AlwaysAutoResize | ImGuiWindowFlags.NoMove | ImGuiWindowFlags.NoFocusOnAppearing);
                    ImGui.Text($"FPS: {_currentFps:F0}");
                    if (_showDebug)
                    {
                        ImGui.Text($"Pos: X={_position.X:F2} Y={_position.Y:F2} Z={_position.Z:F2}");
                        ImGui.Text($"Yaw: {_yaw:F1}  Pitch: {_pitch:F1}");
                        ImGui.Text($"Block: {_selectedBlock}");
                        ImGui.Text($"Hit: ({_hitBlock.X}, {_hitBlock.Y}, {_hitBlock.Z})");
                        ImGui.Text($"Chunks: {_chunks.Count}");
                        ImGui.Separator();
                        long workingSet = Process.GetCurrentProcess().WorkingSet64 / (1024 * 1024);
                        ImGui.Text($"RAM: {workingSet} MB");
                    }
                    ImGui.End();
                }

                int hotbarSlots = 5;
                float slotSize = 50f, border = 3f, totalW = hotbarSlots * slotSize + 2 * border, totalH = slotSize + 2 * border, startX = (ClientSize.X - totalW) / 2f, y = ClientSize.Y - totalH - 10f;
                ImGui.SetNextWindowPos(new System.Numerics.Vector2(startX, y));
                ImGui.SetNextWindowSize(new System.Numerics.Vector2(totalW, totalH));
                ImGui.Begin("Hotbar", ImGuiWindowFlags.NoTitleBar | ImGuiWindowFlags.NoResize | ImGuiWindowFlags.NoMove | ImGuiWindowFlags.NoBackground | ImGuiWindowFlags.NoDecoration | ImGuiWindowFlags.NoScrollbar | ImGuiWindowFlags.NoInputs | ImGuiWindowFlags.NoBringToFrontOnFocus);
                var windowDrawList = ImGui.GetWindowDrawList();
                var pMin = new System.Numerics.Vector2(startX, y);
                var pMax = new System.Numerics.Vector2(startX + totalW, y + totalH);
                windowDrawList.AddRectFilled(pMin, pMax, 0xFF333333);
                windowDrawList.AddRect(pMin, pMax, 0xFF000000, 0f, 0, 2f);
                for (int i = 0; i < hotbarSlots; i++)
                {
                    float offsetX = startX + border + i * slotSize, offsetY = y + border;
                    windowDrawList.AddRectFilled(new System.Numerics.Vector2(offsetX + 1, offsetY + 1), new System.Numerics.Vector2(offsetX + slotSize - 1, offsetY + slotSize - 1), 0xFF8B8B8B);
                    if (_blockTextures[i] != 0) windowDrawList.AddImage((IntPtr)_blockTextures[i], new System.Numerics.Vector2(offsetX + 4, offsetY + 4), new System.Numerics.Vector2(offsetX + slotSize - 4, offsetY + slotSize - 4));
                    if (i + 1 == _selectedBlock) windowDrawList.AddRect(new System.Numerics.Vector2(offsetX - 2, offsetY - 2), new System.Numerics.Vector2(offsetX + slotSize + 2, offsetY + slotSize + 2), 0xFFFFFFFF, 0f, 0, 2f);
                }
                ImGui.End();
            }
        }

        protected override void OnUpdateFrame(FrameEventArgs args)
        {
            base.OnUpdateFrame(args);
            if (_isHosting && (_serverProcess == null || _serverProcess.HasExited)) _isHosting = false;

            if (!SettingsManager.NoFpsLimit && SettingsManager.MaxFps > 0 && VSync == VSyncMode.Off)
            {
                double targetTime = 1.0 / SettingsManager.MaxFps;
                if (args.Time < targetTime) Thread.Sleep((int)((targetTime - args.Time) * 1000));
            }

            int budget = 5000;
            while (budget-- > 0 && _mainThreadActions.TryDequeue(out var action))
            {
                try { action(); } catch (Exception ex) { Console.WriteLine($"[MainThread] {ex.Message}"); }
            }

            // === ЧАНКИ: обработка ===
            UpdateChunksAroundPlayer();

            // Строим 1 грязный чанк за кадр (чтобы не фризить)
            Chunk? toBuild = null;
            foreach (var c in _chunks.Values)
            {
                if (c.Dirty)
                {
                    toBuild = c;
                    break;
                }
            }
            if (toBuild != null) BuildChunkMesh(toBuild);

            // === Сеть ===
            float idt = (float)args.Time;
            float lerp = 1f - MathF.Exp(-InterpSpeed * idt);
            long localNow = DateTimeOffset.UtcNow.ToUnixTimeMilliseconds();
            List<string>? toRemove = null;
            foreach (var rp in _remote.Values)
            {
                if (localNow - rp.LastLocalRecvMs > StaleTimeoutMs) { (toRemove ??= new List<string>()).Add(rp.Name); continue; }
                if (Vector3.Distance(rp.Position, rp.TargetPosition) > 5f) rp.Position = rp.TargetPosition;
                else rp.Position = Vector3.Lerp(rp.Position, rp.TargetPosition, lerp);
            }
            if (toRemove != null) foreach (var n in toRemove) _remote.Remove(n);

            if (_isMultiplayer && _client.Connected && _state == GameState.Playing)
            {
                double now = GLFW.GetTime();
                if (now - _lastPosSend > 0.05) { _client.SendPlayer(_playerName, _position.X, _position.Y, _position.Z); _lastPosSend = now; }
            }

            if (!IsFocused) return;
            var input = KeyboardState;
            float dt = (float)args.Time;
            if (input.IsKeyPressed(Keys.F3)) _showDebug = !_showDebug;
            _showTabMenu = input.IsKeyDown(Keys.Tab);

            if (input.IsKeyPressed(Keys.Escape))
            {
                if (_state == GameState.Playing) { _state = GameState.Paused; CursorState = CursorState.Normal; }
                else if (_state == GameState.Paused) { _state = GameState.Playing; CursorState = CursorState.Grabbed; _firstMove = true; }
                else if (_state == GameState.Inventory) { _state = GameState.Playing; CursorState = CursorState.Grabbed; _firstMove = true; }
                else if (_state == GameState.Settings) { _state = _previousState; if (_state == GameState.Playing) { CursorState = CursorState.Grabbed; _firstMove = true; } else CursorState = CursorState.Normal; }
            }

            if (input.IsKeyPressed(Keys.E))
            {
                if (_state == GameState.Playing) { _state = GameState.Inventory; CursorState = CursorState.Normal; }
                else if (_state == GameState.Inventory) { _state = GameState.Playing; CursorState = CursorState.Grabbed; _firstMove = true; }
            }

            if (_state != GameState.Playing) return;

            float wheel = MouseState.ScrollDelta.Y;
            if (wheel > 0) { _selectedBlock--; if (_selectedBlock < 1) _selectedBlock = 5; }
            else if (wheel < 0) { _selectedBlock++; if (_selectedBlock > 5) _selectedBlock = 1; }

            if (_selectedBlock != _lastSentHeldBlock && _isMultiplayer && _client.Connected) { _lastSentHeldBlock = _selectedBlock; _client.SendHeldBlock(_playerName, _selectedBlock); }

            var mouse = MouseState;
            if (_firstMove) { _lastMousePos = new Vector2(mouse.X, mouse.Y); _firstMove = false; }
            else
            {
                float dx = mouse.X - _lastMousePos.X, dy = mouse.Y - _lastMousePos.Y;
                _lastMousePos = new Vector2(mouse.X, mouse.Y);
                _yaw += dx * SettingsManager.MouseSensitivity;
                _pitch -= dy * SettingsManager.MouseSensitivity;
                _pitch = MathHelper.Clamp(_pitch, -89f, 89f);
                float yawR = MathHelper.DegreesToRadians(_yaw), pitchR = MathHelper.DegreesToRadians(_pitch);
                _front = Vector3.Normalize(new Vector3(MathF.Cos(yawR) * MathF.Cos(pitchR), MathF.Sin(pitchR), MathF.Sin(yawR) * MathF.Cos(pitchR)));
            }

            Vector3 forward = new Vector3(_front.X, 0, _front.Z);
            if (forward.LengthSquared > 0.0001f) forward = Vector3.Normalize(forward);
            Vector3 right = Vector3.Normalize(Vector3.Cross(forward, _up));

            Vector3 wish = Vector3.Zero;
            if (input.IsKeyDown(Keys.W)) wish += forward;
            if (input.IsKeyDown(Keys.S)) wish -= forward;
            if (input.IsKeyDown(Keys.D)) wish += right;
            if (input.IsKeyDown(Keys.A)) wish -= right;
            if (wish.LengthSquared > 0.0001f) wish = Vector3.Normalize(wish);

            MoveWithCollision(wish * MoveSpeed * dt);
            bool onGround = IsOnGround();
            if (onGround && _velocity.Y <= 0) _velocity.Y = 0;
            _velocity.Y -= Gravity * dt;
            if (input.IsKeyDown(Keys.Space) && onGround) _velocity.Y = JumpSpeed;
            MoveWithCollision(new Vector3(0, _velocity.Y * dt, 0));

            if (_position.Y < -20) { _position = new Vector3(_worldManager.CurrentData.SizeX / 2f, 40, _worldManager.CurrentData.SizeZ / 2f); _velocity = Vector3.Zero; }

            if (input.IsKeyDown(Keys.D1)) _selectedBlock = 1;
            if (input.IsKeyDown(Keys.D2)) _selectedBlock = 2;
            if (input.IsKeyDown(Keys.D3)) _selectedBlock = 3;
            if (input.IsKeyDown(Keys.D4)) _selectedBlock = 4;
            if (input.IsKeyDown(Keys.D5)) _selectedBlock = 5;

            Raycast();

            if (MouseState.IsButtonPressed(MouseButton.Left) && _hitBlock.X != -1)
            {
                _worldManager.Blocks[_hitBlock.X, _hitBlock.Y, _hitBlock.Z] = 0;
                MarkChunkDirtyAt(_hitBlock.X, _hitBlock.Z);
                if (_isMultiplayer) _client.SendBlock(_hitBlock.X, _hitBlock.Y, _hitBlock.Z, 0);
                _breakStartTime = GLFW.GetTime();
            }
            else if (MouseState.IsButtonDown(MouseButton.Left) && _hitBlock.X != -1)
            {
                if (_breakStartTime == 0) _breakStartTime = GLFW.GetTime();
                if (GLFW.GetTime() - _breakStartTime > 0.25)
                {
                    _worldManager.Blocks[_hitBlock.X, _hitBlock.Y, _hitBlock.Z] = 0;
                    MarkChunkDirtyAt(_hitBlock.X, _hitBlock.Z);
                    if (_isMultiplayer) _client.SendBlock(_hitBlock.X, _hitBlock.Y, _hitBlock.Z, 0);
                    _breakStartTime = GLFW.GetTime();
                }
            }
            else { _breakStartTime = 0; }

            if (MouseState.IsButtonPressed(MouseButton.Right) && _placeBlock.X != -1)
            {
                int px = _placeBlock.X, py = _placeBlock.Y, pz = _placeBlock.Z;
                int sx = _worldManager.Blocks.GetLength(0), sy = _worldManager.Blocks.GetLength(1), sz = _worldManager.Blocks.GetLength(2);
                if (px >= 0 && px < sx && py >= 0 && py < sy && pz >= 0 && pz < sz && _worldManager.Blocks[px, py, pz] == 0 && !BlockIntersectsPlayer(_placeBlock))
                {
                    _worldManager.Blocks[px, py, pz] = _selectedBlock;
                    MarkChunkDirtyAt(px, pz);
                    if (_isMultiplayer) _client.SendBlock(px, py, pz, _selectedBlock);
                }
                _lastPlaceTime = GLFW.GetTime();
            }
            else if (MouseState.IsButtonDown(MouseButton.Right) && _placeBlock.X != -1 && (GLFW.GetTime() - _lastPlaceTime) > 0.2)
            {
                int px = _placeBlock.X, py = _placeBlock.Y, pz = _placeBlock.Z;
                int sx = _worldManager.Blocks.GetLength(0), sy = _worldManager.Blocks.GetLength(1), sz = _worldManager.Blocks.GetLength(2);
                if (px >= 0 && px < sx && py >= 0 && py < sy && pz >= 0 && pz < sz && _worldManager.Blocks[px, py, pz] == 0 && !BlockIntersectsPlayer(_placeBlock))
                {
                    _worldManager.Blocks[px, py, pz] = _selectedBlock;
                    MarkChunkDirtyAt(px, pz);
                    if (_isMultiplayer) _client.SendBlock(px, py, pz, _selectedBlock);
                    _lastPlaceTime = GLFW.GetTime();
                }
            }
        }

        protected override void OnResize(ResizeEventArgs e)
        {
            base.OnResize(e);
            if (_imGuiController != null) _imGuiController.WindowResized(ClientSize.X, ClientSize.Y);
        }

        static void Main(string[] args)
        {
            var nativeWindowSettings = new NativeWindowSettings()
            {
                ClientSize = new Vector2i(1280, 720),
                Title = "CScraft",
                WindowState = WindowState.Fullscreen
            };
            using (var game = new Game(GameWindowSettings.Default, nativeWindowSettings))
            {
                game.Run();
            }
        }
    }
}