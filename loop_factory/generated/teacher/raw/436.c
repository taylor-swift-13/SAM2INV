int main1(int a,int k){
  int l, j, r, v;

  l=23;
  j=1;
  r=l;
  v=k;

  while (j<=l/2) {
      r = r*r+r;
      r = r%8;
      j = j*2;
  }

}
