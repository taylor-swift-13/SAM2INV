int main74(int t,int o,int x){
  int ns, bp, woy, f2, c5e;

  ns=0;
  bp=-15814;
  woy=3;
  f2=ns;
  c5e=0;

  while (bp+7<0) {
      bp = bp+woy-1;
      woy += 2;
      f2 = f2 + ns;
      c5e = c5e+(woy%9);
      o = o + 3;
      x = x + woy;
  }

}
