int main1(){
  int cd3, yld, g3j, h;

  cd3=63;
  yld=0;
  g3j=0;
  h=0;

  while (h<cd3) {
      g3j += 1;
      h += 1;
  }

  while (1) {
      if (h+1<cd3) {
          h += 4;
      }
      yld += 1;
      if (yld>=cd3) {
          break;
      }
  }

}
