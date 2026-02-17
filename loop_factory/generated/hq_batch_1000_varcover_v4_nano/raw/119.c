int main1(int a,int k,int q){
  int l, i, v, e;

  l=(a%14)+18;
  i=l;
  v=-4;
  e=a;

  while (i>0) {
      v = v+1;
      e = e+v;
      v = v+3;
      i = i-1;
  }

}
