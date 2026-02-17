int main1(int a,int n,int p,int q){
  int l, i, v, r;

  l=p;
  i=l;
  v=a;
  r=n;

  while (i>0) {
      v = v+1;
      r = r+v;
      if (i+3<=p+l) {
          v = v+l;
      }
      else {
          r = a*3;
      }
      r = v-r;
      r = r+v;
      v = v-q;
      i = i-1;
  }

}
