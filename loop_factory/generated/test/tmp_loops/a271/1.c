int main1(int a,int q){
  int l, i, v;

  l=q;
  i=l;
  v=q;

  while (i>0) {
      v = v+i;
      i = i/2;
  }

  while (v<i) {
      v = v+1;
  }

}
