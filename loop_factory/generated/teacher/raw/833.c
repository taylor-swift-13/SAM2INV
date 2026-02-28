int main1(int a,int k,int n){
  int c, t, v, i;

  c=(a%8)+14;
  t=0;
  v=c;
  i=c;

  while (t<c) {
      v = v+1;
      i = i-1;
      if (t+4<=a+c) {
          i = i+1;
      }
      v = v+t;
      t = t+1;
  }

}
