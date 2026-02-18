int main1(int a,int b,int k,int m){
  int l, i, v;

  l=a+20;
  i=l;
  v=i;

  while (i>0) {
      v = v-v;
      if (v+3<l) {
          v = v+v;
      }
      else {
          v = v+v;
      }
      i = i/2;
  }

}
