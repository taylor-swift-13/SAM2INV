int main101(int q,int y,int f){
  int s1, ax, os, wh21, ci, heu, k, u6;

  s1=f-2;
  ax=s1;
  os=0;
  wh21=q;
  ci=y;
  heu=6;
  k=y;
  u6=s1;

  while (1) {
      if (!(os<s1)) {
          break;
      }
      os = os+5+ax%2;
      u6 += 2;
      wh21 += os;
      f = f+s1-ax;
      wh21 = wh21 + ax;
      ci = ci*ci;
  }

  while (1) {
      if (k>=heu) {
          break;
      }
      k += 1;
      s1 += 1;
      q = q + k;
      os += s1;
      y += s1;
      os += ci;
  }

}
