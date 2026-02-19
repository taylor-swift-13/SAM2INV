int main1(int b,int k){
  int l, i, v, j;

  l=(k%36)+11;
  i=l;
  v=0;
  j=i;

  while (i>0) {
      i = i-1;
  }

  while (v<l) {
      j = j+j;
      v = v*3;
  }

}
