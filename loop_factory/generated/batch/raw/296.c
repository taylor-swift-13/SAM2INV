int main1(int b,int k){
  int p, q, v, r;

  p=(k%7)+8;
  q=0;
  v=p;
  r=q;

  while (v<p) {
      if (v<p) {
          v = v+1;
      }
      r = r+r;
      r = r+v;
      v = v+1;
      v = v+r;
      r = v-r;
  }

}
