int main1(int a,int k){
  int c, i, v, r;

  c=36;
  i=0;
  v=k;
  r=c;

  while (i+5<=c) {
      if (v+6<=c) {
          v = v+6;
      }
      else {
          v = c;
      }
      v = v+1;
      r = r+v;
  }

}
