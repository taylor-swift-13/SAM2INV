int main1(int e){
  int v, omo4, xb, q, y;

  v=e;
  omo4=0;
  xb=0;
  q=0;
  y=e;

  while (omo4+7<=v) {
      e = xb+q+y;
      xb += 1;
      q = q + y;
      omo4 = omo4 + 7;
  }

  while (1) {
      y++;
      if (y>=omo4) {
          break;
      }
  }

}
