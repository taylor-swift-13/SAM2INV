int main176(int b,int f,int i){
  int a, rq5, zi, r, cb, w, esd;

  a=(b%9)+18;
  rq5=1;
  zi=0;
  r=rq5;
  cb=11;
  w=1;
  esd=rq5;

  while (1) {
      if (!(zi<a)) {
          break;
      }
      zi += 1;
      if (w<=cb) {
          cb = w;
      }
      b = b + cb;
      f = f + 3;
      r = r + w;
      esd = esd+cb-cb;
  }

}
