int main90(int n,int p,int q){
  int h, a, f;

  h=q;
  a=0;
  f=h;

  while (a<h) {
      f = f+a;
      f = f-f;
      if (f+2<h) {
          f = f+1;
      }
      a = a+2;
  }

}
