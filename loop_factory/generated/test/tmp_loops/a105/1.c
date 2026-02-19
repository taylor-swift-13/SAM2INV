int main1(int a,int b){
  int l, i, v, j;

  l=b;
  i=1;
  v=-1;
  j=-2;

  while (i<l) {
      v = v+j+j;
      v = v+1;
      i = i*3;
  }

  while (j<v) {
      i = i+i;
      j = j+1;
  }

}
