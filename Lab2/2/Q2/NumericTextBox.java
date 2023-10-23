/**
 * This class represents a text box for numeric values.
 * Its content is represented as an array of single digits.
 *
 * Your task is to add JML contracts for each method in this class
 * that reflect the informal descriptions in the Javadoc comments.
 *
 * Also add JML invariants for the fields "cursorPosition" and "content" that make sure that
 *
 *  - the cursorPosition is always a valid value (see comment for cursorPosition).
 *  - the content before the cursor contains only single digits
 *  - the content after the cursor is EMPTY
 *
 * Furthermore, think about which methods are pure and use the appropriate annotation.
 *
 * Hint: If you use variables for array indices in an assignable-clause,
 *       their values are evaluated in the pre-state.
 */
public class NumericTextBox
{
	public final int EMPTY = -1;

	/**
	 * The current cursor position, i.e. the position after the previously entered digit.
	 * If this is 0, then the cursor is placed at the very beginning of the text box.
	 * Note that the number of possible cursor positions is greater by one than
	 * the length of the text box.
	 */

	/*@ public invariant (0 <= cursorPosition 
	  @			&& cursorPosition <= content.length); 
	  @*/
	private /*@ spec_public @*/ int cursorPosition;

    /*@ public invariant (\forall int i;
      @                          0 <= i && i < cursorPosition;
      @                          0 <= content[i] && content[i] <= 9);
      @*/

    /*@ public invariant (\forall int i;
      @                          i >= cursorPosition && i < content.length;
      @                          content[i] == EMPTY);
      @*/

	/**
	 * This array stores the contents of the text box. At every position
	 * before the cursor, there is a valid value (i.e. a single digit).
	 * Positions after the cursor must be EMPTY.
	 */
	private /*@ spec_public @*/ int[] content;

	/**
	 * Holds the current TextBoxRenderer. This can be null, which means that there
	 * is no renderer assigned.
	 */
	private /*@ spec_public nullable @*/ TextBoxRenderer textBoxRenderer;

	/**
	 * Gets the currently assigned TextBoxRenderer.
	 */

    /*@ public normal_behavior
      @ ensures \result == textBoxRenderer;
      @*/
	public /*@ nullable @*/ TextBoxRenderer getRenderer()
	{
		// ...
	}

	/**
	 * Sets the TextBoxRenderer used for rendering this text box.
	 * It can also be set to null, if the text box is not rendered.
	 */

    /*@ public normal_behavior
      @ ensures textBoxRenderer == renderer;
	  @ assignable textBoxRenderer;
      @*/
	public void setRenderer(/*@ nullable @*/ TextBoxRenderer renderer)
	{
		// ...
	}

	/**
	 * Checks whether a given input is a single digit (i.e. between 0 and 9).
	 *
	 * @param input The input character.
	 * @return true if the input is a single digit, false otherwise.
	 */

    /*@ public normal_behavior
      @ ensures \result == (0 <= input && input <= 9);
	  @ assignable \nothing;
      @*/
	public /*@ pure @*/ boolean isSingleDigit(int input)
	{
		// ...
	}

	/**
	 * Clears the text box and resets the cursor to the start.
	 * Also sets the contentChanged flag of the current TextBoxRenderer, if any.
	 */

    /*@ public normal_behavior
      @ ensures (\forall int i;
      @                 0 <= i && i < content.length;
      @                 content[i] == EMPTY);
      @ ensures cursorPosition == 0;
      @ ensures (textBoxRenderer != null ==> textBoxRenderer.contentChanged == false);
	  @ assignable textBoxRenderer.contentChanged, cursorPosition, content[*];
      @*/
	public void clear()
	{
		// ...
	}

	/**
	 * Enters a given input character into the text box and moves the cursor forward.
	 * If the input can be processed, the contentChanged flag of the current TextBoxRenderer (if any) is set.
	 * If an exception occurs, the TextBoxRenderer's showError flag is set instead.
	 *
	 * @param input the input character.
	 *
	 * @throws IllegalArgumentException if the input was not a single digit.
	 *
	 * @throws RuntimeException if the input was valid, but the cursor is at the end
	 *                          of the text box and no further input can be accepted.
	 */

    /*@ public normal_behavior
      @ requires isSingleDigit(input);
	  @ requires cursorPosition != content.length;
      @ ensures content[\old(cursorPosition)] == input;
      @ ensures cursorPosition == \old(cursorPosition) + 1;
      @ ensures (textBoxRenderer != null ==> textBoxRenderer.contentChanged == true);
	  @ assignable content[cursorPosition], cursorPosition, textBoxRenderer.contentChanged;
      @*/

    /*@ public exceptional_behavior
	  @ requires !isSingleDigit(input) || cursorPosition == content.length;
	  @ signals_only IllegalArgumentException, RuntimeException;
      @ signals (IllegalArgumentException) (textBoxRenderer != null ==> textBoxRenderer.showError == true);
      @ signals (RuntimeException) (textBoxRenderer != null ==> textBoxRenderer.showError == true);
	  @ assignable textBoxRenderer.showError;
      @*/
	public void enterCharacter(int input)
	{
		// ...
	}

	/**
	 * Deletes the most recently entered character and moves the cursor back one position.
	 * Also sets the current TextBoxRenderer's contentChanged flag (if any).
	 *
	 * @throws RuntimeException if the cursor is at the very beginning. In this case
	 *                          the showError flag of the TextBoxRenderer is set
	 *                          before the exception is thrown.
	 */

    /*@ public normal_behavior
      @ requires cursorPosition != 0;
      @ ensures content[cursorPosition] == EMPTY;
      @ ensures cursorPosition == \old(cursorPosition) - 1;
      @ ensures (textBoxRenderer != null ==> textBoxRenderer.contentChanged == true);
	  @ assignable content[cursorPosition - 1], cursorPosition, textBoxRenderer.contentChanged;
      @*/

    /*@ public exceptional_behavior
	  @ requires cursorPosition == 0;
      @ signals (RuntimeException) (textBoxRenderer != null ==> textBoxRenderer.showError == true);
	  @ assignable textBoxRenderer.showError;
      @*/
	public void backspace()
	{
		// ...
	}
}

/**
 * This class represents a renderer that is responsible for displaying the
 * text box to the user in some way.
 */
class TextBoxRenderer
{
	/**
	 * Whether the content was changed (so the rendered text box needs a refresh).
	 */
	public boolean contentChanged = false;

	/**
	 * Whether an exception occured (which should be represented in the rendered text box).
	 */
	public boolean showError = false;
}