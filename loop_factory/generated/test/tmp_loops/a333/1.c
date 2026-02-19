int main1(int k,int p){
  int l, i, v;

  l=k+3;
  i=l;
  v=k;

  while (i>0) {
      v = v+1;
      i = i-1;
  }

  while (v<l) {
      i = i+i;
      v = v+1;
  }

}
