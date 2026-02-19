int main1(int a,int m){
  int l, i, v, f;

  l=a+12;
  i=l;
  v=a;
  f=m;

  while (i>0) {
      f = f+f;
      i = i-1;
  }

  while (f<i) {
      f = f*3;
  }

}
