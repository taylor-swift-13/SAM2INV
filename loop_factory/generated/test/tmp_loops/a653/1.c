int main1(int a,int q){
  int l, i, v;

  l=q+15;
  i=l;
  v=i;

  while (i>0) {
      v = v+1;
      v = v+v;
      i = i-1;
  }

  while (v<i) {
      l = l+1;
      v = v+4;
  }

}
