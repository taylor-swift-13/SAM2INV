int main1(int z){
  int d, m, c54;

  d=(z%14)+20;
  m=0;
  c54=d;

  while (m<d) {
      c54 = d-m;
      m = m + 5;
      z += c54;
  }

}
