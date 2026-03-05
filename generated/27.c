int main27(int x,int t){
  int n, rpj, la;

  n=t*2;
  rpj=n;
  la=-4;

  while (1) {
      if (!(rpj-1>=0)) {
          break;
      }
      la++;
      x = x + la;
      t = x-t;
      rpj = rpj - 1;
  }

}
