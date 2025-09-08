# Boz — Whatsapp bot
### *primeira gambiarra profissa que fiz* 

<div align="center">

[![Status](https://img.shields.io/badge/🚀_status-alpha_release-FF6B35?style=for-the-badge&labelColor=1a1a1a)](https://github.com/)
[![Node](https://img.shields.io/badge/⚡_node-%3E=_18_LTS-339933?style=for-the-badge&labelColor=1a1a1a&logo=nodedotjs)](https://nodejs.org/)
[![License](https://img.shields.io/badge/📄_license-MIT-00ADD8?style=for-the-badge&labelColor=1a1a1a)](LICENSE)
[![WhatsApp](https://img.shields.io/badge/💬_WhatsApp-Ready-25D366?style=for-the-badge&labelColor=1a1a1a&logo=whatsapp)](https://www.whatsapp.com)
[![Made with](https://img.shields.io/badge/💖_made_with-coffee_%26_insomnia-D4AF37?style=for-the-badge&labelColor=1a1a1a)](https://github.com/)

</div>

<div align="center">
  <h1>🎯 MEU PRIMEIRO PROJETO SÉRIO</h1>
  <h3>🚀 Bot maroto que transforma qualquer mídia em figurinha otimizada</h3>
  <p><strong>Baixa áudio/vídeo, comprime tudo e gerencia fila como um chefe</strong></p>
  <p><em>Feito com Baileys + ffmpeg + sharp + muito café </em> ☕💻</p>
</div>

<div align="center">
  
  ```
  ┌─────────────────────────────────────────────────────┐
  │  🎊 PRIMEIRO PROJETO QUE NÃO DEU MERDA TOTAL! 🎊   │
  │                                                     │
  │  ✅ Funciona de verdade                            │
  │  ✅ Não quebra a cada 5 minutos                    │
  │  ✅ Parece que sei o que tô fazendo                │
  │  ✅ Minha mãe finalmente orgulhosa                 │
  └─────────────────────────────────────────────────────┘
  ```
  
</div>

---

## 📋 Navegação Rápida

<div align="center">

| 🎯 **Essencial** | 🛠️ **Técnico** | 🎨 **Extra** |
|:---:|:---:|:---:|
| [💡 O que faz](#-o-que-essa-belezinha-faz) | [📋 Requisitos](#-requisitos-pra-rodar) | [🎊 Galeria](#-galeria-de-sucessos) |
| [🚀 Instalação](#-instalação-express) | [⚙️ Configuração](#️-configuração) | [🏆 Conquistas](#-conquistas-desbloqueadas) |
| [👑 Ser Admin](#-virar-o-chefão) | [🔐 Segurança](#-segurança-modo-ninja) | [💭 Agradecimentos](#-hall-da-fama) |

</div>

---

## 💡 O que essa belezinha faz

<div align="center">

### 🎨 **TRANSFORMAÇÃO MÁGICA DE MÍDIA**

</div>

🖼️ **Pega qualquer bagulho** → Imagem, GIF, vídeo, áudio  
⚡ **Vira sticker** → WebP otimizado, animado ou estático  
🎯 **Sempre no limite** → Comprime pra caber no 1MB sagrado  
🤖 **Automático total** → Manda, espera, recebe. Simples assim!

### 🔥 **Features que me deixaram orgulhoso**

<div align="center">

| 🌟 **O que me custou o sono** |
|:---:|
| 🎨 Conversão inteligente de qualquer formato pra WebP |
| ⚡ Sistema de fila com prioridades (nada de travamento!) |
| 🧠 Compressão adaptativa (tenta várias vezes até dar certo) |
| 🔄 Retry system (porque nem tudo dá certo na primeira) |
| 📱 Rate-limiter (pra não ser banido do WhatsApp) |
| 🎵 Integração YouTube (baixa música/vídeo direto no chat) |
| 🤖 IA Gemini (quando tô me sentindo ambicioso) |

</div>

> **Plot twist:** Começou como "só quero fazer um bot de sticker" e virou essa obra de arte! 🎭

---

## ⚡ Arsenal Técnico

<div align="center">

### 🛠️ **STACK DE GUERRA**

| Tecnologia | Por que escolhi | Status |
|:---:|:---:|:---:|
| **🔌 Baileys** | Única lib que não me fez chorar | ✅ Domado |
| **🎨 Sharp** | Processa imagem que é uma beleza | ✅ Master |
| **🎬 FFmpeg** | Pra mexer com vídeo como um pro | ✅ Apanhei mas aprendi |
| **📦 Node.js** | Porque JavaScript é vida | ✅ Fluente |
| **⚡ ffmpeg-static** | Pra não quebrar no servidor | ✅ Salva-vidas |

</div>

### 🎯 **Funcionalidades que funcionam DE VERDADE**

```javascript
// Isso aqui realmente funciona, juro! 🤞
🔥 Conexão WebSocket estável (95% uptime na minha casa)
🎨 Pool de workers FFmpeg (paralelismo que dá gosto)  
📊 Cache inteligente (menos processamento = mais velocidade)
🔄 Reconexão automática (porque internet BR é assim mesmo)
⚡ Cleanup de memória (aprendi isso na marra)
🎵 Download YouTube/Tiktoker (modo hacker ativado)
👾 Visualize o Status do bot (util dms)
```

---

## 📋 Requisitos pra rodar

<div align="center">

### 🎯 **CHECKLIST DA SOBREVIVÊNCIA**

</div>

| Item | Versão | Onde conseguir | Criticidade |
|:---:|:---:|:---:|:---:|
| **☕ Node.js** | v18+ | [nodejs.org](https://nodejs.org/) | 🔴 OBRIGATÓRIO |
| **📦 npm/yarn** | Latest | Vem com o Node | 🔴 OBRIGATÓRIO |  
| **🎵 yt-dlp** | Latest | `pip install yt-dlp` | 🟡 Só pra YouTube |
| **🎬 ffmpeg** | Qualquer | No PATH ou usa o static | 🟡 Recomendado |
| **💾 Espaço/RAM** | ~1GB/500MB | HD/SSD | 🟢 Tranquilo |

<div align="center">

```bash
# Comando mágico pra verificar se tá tudo OK
node --version   # deve mostrar v18+
npm --version    # qualquer versão serve
yt-dlp --version # opcional, só pra YouTube
ffmpeg -version  # opcional, o bot tem um builtin
```

</div>

---

## 🚀 Instalação Express

### 1️⃣ **Clonagem Style**
```bash
git clone <seu-repo-aqui>
cd <nome-do-projeto>
```

### 2️⃣ **Instalação das Deps** 
```bash
npm install
# ou se você é team yarn
yarn install
```

### 3️⃣ **Criação das Pastas Sagradas**
```bash
mkdir -p data
mkdir -p tmp/whatsapp-bot-boz
# No Windows: md data && md tmp\whatsapp-bot-boz
```

### 4️⃣ **O Grande Momento** 🥁
```bash
node boz.js
# ou pra modo turbinado
node --expose-gc boz.js
```

<div align="center">

### 🎊 **SE APARECEU UM QR CODE, VOCÊ É FODA!** 🎊

```
┌─────────────────────────────┐
│  📱 Abre o WhatsApp          │
│  ⚙️  Dispositivos Vinculado │  
│  📷 Escaneia o QR           │
│  🎉 SUCESSO TOTAL!          │
└─────────────────────────────┘
```
(caso não aparece, terá um link abaixo)

</div>

---

## ⚙️ Configuração

### 🎛️ **Central de Comando**

Procura essas linhas no código e personaliza do teu jeito:

```javascript
// 🏠 Onde tudo mora
const AUTH_FOLDER = '/data/auth_info_baileys';    // Sessão WhatsApp  
const TEMP_FOLDER = '/tmp/whatsapp-bot-boz';      // Arquivos temporários
const TAGS_FILE = path.join('/data', 'tags.json'); // Dados salvos

// 🔑 Suas chaves secretas
const YOUTUBE_API_KEY = 'SUA_API_YOUTUBE_AQUI';   // YouTube Data API
const GEMINI_API_KEY = 'SUA_GEMINI_API_AQUI';     // Google AI Studio  
const ADMIN_NUMBER = '556392118626@s.whatsapp.net'; // SEU número aqui!
```

### 💡 **Dica de Mestre** 

**JAMAIS** deixe API keys no código! Usa `.env`:

```bash
# Cria o arquivo .env
YOUTUBE_API_KEY=sua_key_aqui
GEMINI_API_KEY=sua_outra_key
ADMIN_NUMBER=5511999887766@s.whatsapp.net
```

```javascript
// No código, usa assim:
require('dotenv').config();
const YOUTUBE_API_KEY = process.env.YOUTUBE_API_KEY;
```

---

## 👑 Virar o Chefão

<div align="center">

### 🎯 **PODER SUPREMO ATIVADO**

</div>

Muda essa linha pro SEU número (formato internacional):

```javascript
const ADMIN_NUMBER = '5511999887766@s.whatsapp.net';
//                    ^^   ^^^    ^^^^
//                    BR   DDD   número
```

### 📱 **Como descobrir seu número no formato certo**

```javascript
// Cole seu número aqui: +55 (11) 99988-7766
// Vira isso: 5511999887766@s.whatsapp.net
//            55 + 11 + 999887766 + @s.whatsapp.net
```

<div align="center">

**🎊 PARABÉNS! Agora você é o REI DO BOT! 👑**

*Comandos exclusivos, QR code, controle total...*

</div>

---

## 🎊 Galeria de Sucessos

<div align="center">

### 🏆 **MOMENTOS ÉPICOS QUE ME DEIXARAM FELIZ**

| Conquista | Descrição | Sentimento |
|:---:|:---:|:---:|
| **✨ Primeiro sticker** | Funcionou na primeira! | 🤯 Incredulidade |
| **🔥 100 conversões** | Sistema estável por horas | 😭 Lágrimas de alegria |
| **⚡ Fila zerada** | Processamento em paralelo | 🚀 Orgulho extremo |
| **📱 Zero crashes** | 24h rodando sem parar | 🏆 Sensação de deus |

</div>

```
💬 Feedback real dos usuários (juro):
   "Caramba, esse bot é rápido!"
   "Melhor que app pago que uso"  
   "Pode ensinar como fez?"
   "Contrata esse moleque!"
```

---

## 🏆 Conquistas Desbloqueadas

<div align="center">

### 🎮 **ACHIEVEMENT UNLOCKED**

</div>

🥇 **"Hello World Turbinado"** — Primeiro projeto que impressiona  
🥈 **"Stack Master"** — Dominou Node.js + libs complexas  
🥉 **"Problem Solver"** — Resolveu compressão automática  
🏅 **"Performance King"** — Sistema de fila eficiente  
⭐ **"User Experience"** — Bot que people realmente usam  
🎯 **"Production Ready"** — Código que roda sem supervisão  

---

## 🔐 Segurança Modo Ninja

<div align="center">

### ⚠️ **REGRAS DE SOBREVIVÊNCIA NO GITHUB**

</div>

🚫 **JAMAIS commitar:**
- `data/auth_info_baileys/` (sessão WhatsApp)
- `cookies.txt` (dados sensíveis) 
- `.env` (suas chaves secretas)
- `tmp/` (lixo temporário)

### 🛡️ **.gitignore da salvação**

```gitignore
# 🔐 Dados sensíveis  
.env
data/auth_info_baileys/
cookies.txt

# 🗑️ Lixo temporário
tmp/
tmp/whatsapp-bot-boz/
node_modules/

```

<div align="center">

**🎯 Golden Rule: Se tem password, não vai pro GitHub!**

</div>

---

## 💭 Hall da Fama

<div align="center">

### 🙏 **MESTRES QUE TORNARAM ISSO POSSÍVEL**

</div>

| 🌟 **Biblioteca** | 👨‍💻 **Criador(es)** | 🎯 **O que faz** | 💖 **Gratidão** |
|:---:|:---:|:---:|:---:|
| **[Baileys](https://github.com/WhiskeySockets/Baileys)** | WhiskeySockets | WhatsApp Web API | Sem você, nada existiria |
| **[Sharp](https://github.com/lovell/sharp)** | Lovell Fuller | Processa imagem | Velocidade de outro mundo |
| **[FFmpeg](https://ffmpeg.org/)** | FFmpeg Team | Multimedia framework | O canivete suíço da mídia |
| **[Node.js](https://nodejs.org/)** | Ryan Dahl & Team | JavaScript runtime | A base de tudo |

### 🎵 **Musicas que me manteve acordado**

```
🎧 PixiesOfficial -  Where Is My Mind?
🎧 YONLAPA - I'm Just Like That
🎧 Calva Louise - Con Corazón
🎧 Radiohead - Creep
```

### ☕ **Combustível do projeto**

- **17 xícaras** de café expresso
- **8L Água** (modo emergência)
- **3 pão seco** de madrugada
- **∞ biscoitos** de chocolate

---

## 🛠️ SOS - Troubleshooting

<div align="center">

### 🚨 **GUIA DE SOBREVIVÊNCIA**

</div>

| 💀 **Erro** | 🎯 **Solução** | ⭐ **Dica Extra** |
|:---:|:---:|:---:|
| `ENOENT: no such file` | `mkdir -p data tmp/whatsapp-bot-boz` | Sempre cria as pastas primeiro |
| `yt-dlp: command not found` | `pip install -U yt-dlp` | Ou baixa o binário |
| `Sticker > 1MB` | Bot tenta várias compressões | Reduz resolução da imagem original |
| `Connection lost` | Bot reconecta sozinho em 30s | Paciência, grasshopper |
| `global.gc not available` | Roda com `--expose-gc` | Só pra monitoramento avançado |

---

<div align="center">

# 🎊 MISSÃO CUMPRIDA! 🎊

### **MEU PRIMEIRO PROJETO QUE:**
✅ **Funciona de verdade**  
✅ **Impressiona os colega**  
✅ **Roda sem quebrar**  
✅ **Tem cara de profissional**  

---

## 🎯 **SE CHEGOU ATÉ AQUI...**

**Você é um verdadeiro guerreiro!** 🛡️⚔️  
*Agora vai lá e faz a sua própria gambiarra profissa!*

[![⭐ STAR](https://img.shields.io/badge/⭐_SE_CURTIU,_DÁ_UMA_STAR-FFD700?style=for-the-badge&logo=github&logoColor=black&labelColor=1a1a1a)](https://github.com/)
[![🍴 FORK](https://img.shields.io/badge/🍴_FORK_E_MELHORE-FF6B35?style=for-the-badge&logo=github&logoColor=white&labelColor=1a1a1a)](https://github.com/)
[![💬 FEEDBACK](https://img.shields.io/badge/💬_ME_CONTA_O_QUE_ACHOU-25D366?style=for-the-badge&logo=whatsapp&logoColor=white&labelColor=1a1a1a)](https://github.com/)

---

### 💭 *Pensamento final*
*"Todo mundo tem que começar de algum lugar. Este foi o meu."* 

**— Dev que  não desistiu** 

</div>

---

<div align="center">
  <sub> Aviso: O projeto está em desenvolvimento, atualmente roda em qualquer maquina com 500 mb de ram e 5 GB (depedendo da escala)</sub><br>
  <sub>💡 Made with insomnia, caffeine & pure determination in 2024</sub>
</div>
