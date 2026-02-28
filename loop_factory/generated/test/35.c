int main35(int k,int p,int q){
  int r, l, v;

  r=34;
  l=0;
  v=2;

  while (1) {
      v = v+2;
      v = v-v;
  }

  while (1) {
      l = l+4;
      if (p*p<=r+5) {
          l = l*2;
      }
      else {
          l = l*l+l;
      }
  }


  /*@ assert \false; */
}
