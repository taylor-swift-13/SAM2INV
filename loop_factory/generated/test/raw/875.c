int main1(int h){
  int md, su, e9, c;

  md=10;
  su=1;
  e9=md;
  c=0;

  while (1) {
      if (!(su<md)) {
          break;
      }
      c = c + 1;
      e9 = c*c;
      su = md;
  }

}
