int main1(int b,int q){
  int r, o, v, f;

  r=(q%30)+18;
  o=0;
  v=-3;
  f=r;

  while (1) {
      if (o>=r) {
          break;
      }
      v = v+1;
      o = o+1;
      v = v+5;
      f = f+2;
      v = v+1;
  }

}
