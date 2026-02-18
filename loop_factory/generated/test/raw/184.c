int main1(int b,int k,int m,int q){
  int l, i, v;

  l=(m%10)+13;
  i=0;
  v=-5;

  while (i<l) {
      v = v+i;
      v = v-v;
      if (m<m+4) {
          v = v+1;
      }
      i = i+1;
  }

}
