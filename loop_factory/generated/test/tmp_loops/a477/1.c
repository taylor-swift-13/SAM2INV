int main1(int m,int p){
  int l, i, v, j;

  l=p-3;
  i=0;
  v=l;
  j=l;

  while (i<l) {
      v = v+j+j;
      v = v+1;
      i = i+1;
  }

  while (j>0) {
      j = j-1;
  }

}
