int main8(int a,int n,int q){
  int h, s, m, v, p;

  h=16;
  s=0;
  m=a;
  v=h;
  p=s;

  while (1) {
      if (p<=v) {
          v = p;
      }
      m = m+1;
      m = m*2;
  }

  while (m-2>=0) {
      v = v+p;
  }

  while (h-3>=0) {
      m = m+3;
      m = m+(-2);
  }

}
