int main1(){
  int h61, wh6r, xy;

  h61=10;
  wh6r=0;
  xy=0;

  while (1) {
      if (!(wh6r < h61)) {
          break;
      }
      xy = ((xy + wh6r) <= h61) * (xy + wh6r) + ((xy + wh6r) > h61) * h61;
      wh6r = h61;
  }

}
