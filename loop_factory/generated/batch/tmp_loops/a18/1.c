int main1(int a,int n){
  int h, k, v, i;

  h=n+20;
  k=h;
  v=n;
  i=n;

  while (k-2>=0) {
      if (k<h/2) {
          v = v+i;
      }
      else {
          v = v*i;
      }
      v = v*2;
      i = i+v;
  }

}
