int main165(int d,int y){
  int dy9, yvp, c, in, x7h, l;

  dy9=d+25;
  yvp=0;
  c=d+25;
  in=1;
  x7h=1;
  l=dy9;

  while (yvp<=dy9-1) {
      if (yvp%9==0) {
          yvp = yvp + 1;
      }
      else {
          if (yvp%7==0) {
              yvp = yvp + 1;
          }
          else {
              if (yvp%5==0) {
                  yvp = yvp + 1;
              }
              else {
                  yvp = yvp + 1;
              }
          }
      }
      yvp = yvp + 1;
      d = (d+yvp)%9;
  }

  while (1) {
      if (!(in<=c)) {
          break;
      }
      x7h = x7h+2*in-1;
      d = d + x7h;
      l = l + 3;
      y++;
      in += 1;
  }

}
