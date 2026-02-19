int main1(int k,int m){
  int l, i, v, q;

  l=m;
  i=l;
  v=i;
  q=i;

  while (i>0) {
      q = q+q;
      i = i-1;
  }

  while (i<l) {
      v = v-v;
      v = v-q;
      i = i+3;
  }

}
