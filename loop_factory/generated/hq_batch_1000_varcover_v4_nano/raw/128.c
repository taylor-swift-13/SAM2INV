int main1(int b,int p,int q){
  int l, i, v;

  l=40;
  i=0;
  v=-8;

  while (i<l) {
      if (v+3<l) {
          v = v-v;
      }
      else {
          v = v+6;
      }
      v = v+i;
      v = v+v;
      v = v+v;
      i = i+1;
  }

}
