int main89(int d){
  int pb, ln, u, v, vchv, ih;

  pb=55;
  ln=pb;
  u=2;
  v=8;
  vchv=ln;
  ih=4;

  while (1) {
      if (!(ln<pb)) {
          break;
      }
      ln += 1;
      u += 6;
      v += 6;
      d += 2;
      vchv += v;
      ih += v;
  }

}
