int main1(int a,int b){
  int q, e, v;

  q=b;
  e=q+2;
  v=0;

  while (e>=1) {
      if ((e%5)==0) {
          v = v*v+v;
      }
      else {
          v = v*v+v;
      }
      e = e/2;
  }

}
