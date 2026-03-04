int main13(int n,int p,int q){
  int f, y, v;

  f=q;
  y=0;
  v=p;

  while (y<f) {
      v = v*v;
      v = v*2;
      y = y+3;
  }

  while (v<y) {
      f = f+1;
      f = v+(-2);
      v = v+3;
  }

}
