int main1(int b,int k){
  int l, i, v;

  l=(k%8)+6;
  i=l;
  v=i;

  while (i>0) {
      i = i-1;
  }

  while (l<i) {
      v = v+l;
      v = v+v;
      l = l+1;
  }

}
