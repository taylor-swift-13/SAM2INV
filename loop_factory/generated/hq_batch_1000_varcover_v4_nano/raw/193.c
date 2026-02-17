int main1(int b,int k,int n){
  int l, i, v;

  l=(n%11)+10;
  i=0;
  v=i;

  while (i<l) {
      v = v-v;
      v = b;
      if ((i%5)==0) {
          v = v-v;
      }
      else {
          v = v+i;
      }
      v = v+i;
      i = i+1;
  }

}
