int main1(int a,int k){
  int l, i, v, m;

  l=(k%7)+13;
  i=l;
  v=i;
  m=a;

  while (i>0) {
      v = v+1;
      m = m-1;
  }

  while (m>0) {
      v = v+m;
      m = m-1;
  }

}
