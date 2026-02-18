int main1(int k,int q){
  int l, i, v;

  l=(q%12)+5;
  i=0;
  v=q;

  while (i<l) {
      if (v+4<l) {
          v = v*v+v;
      }
      else {
          v = v*v;
      }
      i = i+1;
  }

}
