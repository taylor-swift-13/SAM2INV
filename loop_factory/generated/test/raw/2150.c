int main1(){
  int n5, d3, r6, i;

  n5=(1%30)+8;
  d3=0;
  r6=0;
  i=d3;

  while (d3 < n5) {
      r6 = r6 + (d3 * (d3 + 1)) / 2;
      d3++;
      i = (r6)+(i);
      i = i + 1;
  }

}
