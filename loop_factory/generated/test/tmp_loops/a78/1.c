int main1(int k,int q){
  int l, i, v, h;

  l=(q%39)+17;
  i=l;
  v=-5;
  h=-3;

  while (i>0) {
      v = v+3;
      i = i-1;
  }

  while (i<l) {
      h = h+h;
      h = h+1;
      i = i+1;
  }

}
