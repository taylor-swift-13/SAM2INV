int main30(int n,int y,int s){
  int mc, fn, ec1, v;

  mc=n;
  fn=n;
  ec1=0;
  v=1;

  while (fn<=mc) {
      ec1 = ec1*fn;
      if (fn<mc) {
          v = v*fn;
      }
      fn += 1;
      n = n + 5;
      s = s + ec1;
      y += n;
  }

}
