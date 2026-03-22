int main1(int s){
  int o, ws, p0, ppk, v, ytwk, lgw, w;

  o=(s%20)+9;
  ws=2;
  p0=5;
  ppk=0;
  v=ws;
  ytwk=151;
  lgw=ytwk;
  w=ws;

  while (p0<=o) {
      ppk = ppk+p0*p0;
      s += ws;
      v += 2;
      p0++;
  }

  while (1) {
      if (!(lgw-4>=0)) {
          break;
      }
      w += 1;
      s -= 1;
      lgw -= 4;
  }

}
