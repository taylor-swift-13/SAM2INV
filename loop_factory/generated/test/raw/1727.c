int main1(int z){
  int ba, is, wy, h4, l;

  ba=(z%24)+20;
  is=0;
  wy=is;
  h4=z;
  l=ba;

  while (1) {
      if (!(is < ba)) {
          break;
      }
      wy--;
      is++;
      l--;
      h4 += z;
  }

}
