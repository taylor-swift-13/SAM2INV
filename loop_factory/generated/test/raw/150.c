int main1(int a,int m,int n,int p){
  int l, i, v, u, q;

  l=a+7;
  i=0;
  v=a;
  u=3;
  q=5;

  while (i<l) {
      v = v+1;
      u = u+v;
      q = q+u;
      v = v+q;
      u = q-u;
      i = i+1;
  }

}
