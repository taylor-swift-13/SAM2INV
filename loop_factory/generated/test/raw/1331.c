int main1(int f){
  int u97, k3l, hz20, q;

  u97=f+14;
  k3l=0;
  hz20=1;
  q=1;

  while (1) {
      if (!(hz20<=u97)) {
          break;
      }
      k3l += 1;
      q += 2;
      hz20 = hz20 + q;
      f = f + q;
  }

}
