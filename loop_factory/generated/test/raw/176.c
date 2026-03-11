int main1(int a){
  int se8x, l9, l, dt, co, n;

  se8x=a;
  l9=0;
  l=43;
  dt=0;
  co=1;
  n=0;

  while (1) {
      if (!(l>0&&l9<se8x)) {
          break;
      }
      if (l<=co) {
          n = l;
      }
      else {
          n = co;
      }
      l9 = l9 + 1;
      dt += n;
      co = co + 1;
      l -= n;
  }

}
