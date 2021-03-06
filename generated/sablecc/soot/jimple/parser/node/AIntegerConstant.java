/* This file was generated by SableCC (http://www.sablecc.org/). */

package soot.jimple.parser.node;

import soot.jimple.parser.analysis.*;

@SuppressWarnings("nls")
public final class AIntegerConstant extends PConstant
{
    private TMinus _minus_;
    private TIntegerConstant _integerConstant_;

    public AIntegerConstant()
    {
        // Constructor
    }

    public AIntegerConstant(
        @SuppressWarnings("hiding") TMinus _minus_,
        @SuppressWarnings("hiding") TIntegerConstant _integerConstant_)
    {
        // Constructor
        setMinus(_minus_);

        setIntegerConstant(_integerConstant_);

    }

    @Override
    public Object clone()
    {
        return new AIntegerConstant(
            cloneNode(this._minus_),
            cloneNode(this._integerConstant_));
    }

    public void apply(Switch sw)
    {
        ((Analysis) sw).caseAIntegerConstant(this);
    }

    public TMinus getMinus()
    {
        return this._minus_;
    }

    public void setMinus(TMinus node)
    {
        if(this._minus_ != null)
        {
            this._minus_.parent(null);
        }

        if(node != null)
        {
            if(node.parent() != null)
            {
                node.parent().removeChild(node);
            }

            node.parent(this);
        }

        this._minus_ = node;
    }

    public TIntegerConstant getIntegerConstant()
    {
        return this._integerConstant_;
    }

    public void setIntegerConstant(TIntegerConstant node)
    {
        if(this._integerConstant_ != null)
        {
            this._integerConstant_.parent(null);
        }

        if(node != null)
        {
            if(node.parent() != null)
            {
                node.parent().removeChild(node);
            }

            node.parent(this);
        }

        this._integerConstant_ = node;
    }

    @Override
    public String toString()
    {
        return ""
            + toString(this._minus_)
            + toString(this._integerConstant_);
    }

    @Override
    void removeChild(@SuppressWarnings("unused") Node child)
    {
        // Remove child
        if(this._minus_ == child)
        {
            this._minus_ = null;
            return;
        }

        if(this._integerConstant_ == child)
        {
            this._integerConstant_ = null;
            return;
        }

        throw new RuntimeException("Not a child.");
    }

    @Override
    void replaceChild(@SuppressWarnings("unused") Node oldChild, @SuppressWarnings("unused") Node newChild)
    {
        // Replace child
        if(this._minus_ == oldChild)
        {
            setMinus((TMinus) newChild);
            return;
        }

        if(this._integerConstant_ == oldChild)
        {
            setIntegerConstant((TIntegerConstant) newChild);
            return;
        }

        throw new RuntimeException("Not a child.");
    }
}
