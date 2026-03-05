int main83(int d){
  int n, h, u, vy, wh5, jw, c;

  n=d+22;
  h=0;
  u=(d%20)+5;
  vy=25;
  wh5=n;
  jw=d;
  c=h;

  while (1) {
      if (!(u>0)) {
          break;
      }
      u--;
      c = c + u;
      d += h;
      vy += wh5;
      wh5 = wh5 + jw;
      jw += 4;
  }

}
