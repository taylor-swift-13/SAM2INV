int main75(int b,int k,int p){
  int l, s, e;

  l=b-2;
  s=l+7;
  e=2;

  while (s-l>0) {
      if (e==1) {
          e = 2;
      }
      else {
          if (e==2) {
              e = 1;
          }
      }
      e = e*e;
  }

}
