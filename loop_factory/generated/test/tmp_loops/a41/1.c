int main1(int a,int k){
  int l, i, v;

  l=(a%32)+10;
  i=l;
  v=k;

  while (i>0) {
      v = v+v;
      v = v+i;
      i = i-1;
  }

  while (v<l) {
      v = v+1;
  }

}
