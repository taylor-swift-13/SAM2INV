int main1(int a,int m){
  int p, w, t, f;

  p=46;
  w=2;
  t=a;
  f=a;

  while (t!=0&&f!=0) {
      if (t>f) {
          t = t-f;
      }
      else {
          f = f-t;
      }
  }

}
