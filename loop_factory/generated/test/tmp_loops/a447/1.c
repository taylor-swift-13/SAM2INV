int main1(int b,int k){
  int l, i, v, j;

  l=(b%9)+13;
  i=l;
  v=l;
  j=b;

  while (i>0) {
      v = v+3;
      i = i-1;
  }

  while (v>0) {
      l = l-l;
      v = v-1;
  }

}
