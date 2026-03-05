int main171(int s,int e,int w){
  int tv, by, u4, heh, iz;

  tv=w-8;
  by=-3;
  u4=w;
  heh=0;
  iz=(w%6)+2;

  while (1) {
      if (heh>=tv) {
          break;
      }
      by = by*iz+w;
      u4 = u4*iz;
      heh = heh + 1;
      iz += 1;
      w = w + heh;
  }

}
