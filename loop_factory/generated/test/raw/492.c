int main1(){
  int k6cx, bx, op, an, vwe, yb;

  k6cx=1;
  bx=0;
  op=(1%28)+10;
  an=-3;
  vwe=0;
  yb=-2;

  while (op>bx) {
      op -= bx;
      vwe = vwe/2;
      bx = (1)+(bx);
      an = an*2;
      yb += k6cx;
  }

  while (op>yb) {
      op = op - yb;
      yb = (1)+(yb);
      vwe = vwe + op;
      if ((k6cx%5)==0) {
          vwe = vwe*vwe;
      }
  }

}
