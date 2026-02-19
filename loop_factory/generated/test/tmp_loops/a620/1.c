int main1(int k,int n){
  int l, i, v, r;

  l=(k%26)+9;
  i=0;
  v=-1;
  r=i;

  while (i<l) {
      v = v+1;
      r = r-1;
  }

  while (v>0) {
      i = i+4;
      v = v-1;
  }

}
