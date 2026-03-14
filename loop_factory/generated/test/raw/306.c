int main1(){
  int ne, l5qd, y, e1, b7;

  ne=1;
  l5qd=0;
  y=0;
  e1=0;
  b7=ne;

  while (l5qd<=ne-1) {
      y++;
      e1 = e1 + y;
      l5qd = ne;
  }

  while (1) {
      if (!(b7<ne)) {
          break;
      }
      y = ne-b7;
      b7 = b7 + 1;
      y = y + y;
  }

}
