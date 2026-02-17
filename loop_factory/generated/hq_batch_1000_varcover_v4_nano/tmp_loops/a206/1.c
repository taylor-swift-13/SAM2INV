int main1(int a,int m,int n,int p){
  int l, i, v, j, q, e, o;

  l=a+7;
  i=1;
  v=0;
  j=i;
  q=p;
  e=-1;
  o=p;

  while (i<l) {
      e = e*e+v;
      v = v%8;
      v = v%6;
      i = i*3;
  }

}
