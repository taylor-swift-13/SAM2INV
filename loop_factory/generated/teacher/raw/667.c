int main1(int m,int n){
  int j, b, v, a;

  j=m;
  b=0;
  v=n;
  a=j;

  while (1) {
      if (b>=j) {
          break;
      }
      v = v+1;
      b = b+1;
      v = v+1;
      a = a-1;
      a = a+b;
  }

}
