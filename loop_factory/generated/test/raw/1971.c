int main1(int d){
  int fe, f0, nr5, w;

  fe=38;
  f0=0;
  nr5=f0;
  w=0;

  while (f0 < fe) {
      f0 = f0 + 1;
      w = w + d * (f0 >= fe);
      nr5 = nr5 + d * (f0 >= fe);
  }

}
